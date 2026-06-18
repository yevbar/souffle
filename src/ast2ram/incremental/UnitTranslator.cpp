/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnitTranslator.cpp
 *
 * Implements the incremental unit translator (see header).
 *
 ***********************************************************************/

#include "ast2ram/incremental/UnitTranslator.h"
#include "RelationTag.h"
#include "ast/Aggregator.h"
#include "ast/Clause.h"
#include "ast/Negation.h"
#include "ast/Program.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/TopologicallySortedSCCGraph.h"
#include "ast/utility/Visitor.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ram/Assign.h"
#include "ram/Clear.h"
#include "ram/Condition.h"
#include "ram/Conjunction.h"
#include "ram/EmptinessCheck.h"
#include "ram/Erase.h"
#include "ram/Exit.h"
#include "ram/Insert.h"
#include "ram/IntrinsicOperator.h"
#include "ram/Loop.h"
#include "ram/MergeExtend.h"
#include "ram/Node.h"
#include "ram/Query.h"
#include "ram/Relation.h"
#include "ram/Scan.h"
#include "ram/Sequence.h"
#include "ram/Statement.h"
#include "ram/Swap.h"
#include "ram/True.h"
#include "ram/TupleElement.h"
#include "ram/UnsignedConstant.h"
#include "ram/Variable.h"
#include "ram/utility/Visitor.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cstddef>
#include <set>
#include <string>
#include <vector>

namespace souffle::ast2ram::incremental {

namespace {
// The staging relations that hold tuples inserted into / deleted from <R> for the next update.
std::string diffPlusName(const ast::Relation* rel) {
    return getConcreteRelationName(rel->getQualifiedName(), "diff_plus_");
}
std::string diffMinusName(const ast::Relation* rel) {
    return getConcreteRelationName(rel->getQualifiedName(), "diff_minus_");
}
// A nullary "this stratum ran" flag — the cheap dirty signal the guard reads downstream (replaces copying the
// whole relation into diff_plus/diff_minus just to signal a change). The driver purges it between updates,
// like the diff relations (an @-prefix would make it a temporary that a RAM transform removes as unused).
std::string dirtyName(const ast::Relation* rel) {
    return getConcreteRelationName(rel->getQualifiedName(), "__dirty_");
}
// A temporary (@-prefixed, so its Clear is unconditional even inside a subroutine) used to empty a relation
// cheaply: Swap(R, @swap_R) moves R's contents into the temp (an O(1) btree content swap — see the Swap
// synthesiser visitor), which is then bulk-purged, far cheaper than erasing R tuple by tuple.
std::string swapName(const ast::Relation* rel) {
    return getConcreteRelationName(rel->getQualifiedName(), "@swap_");
}

// Rewrites one clause's RAM into a delta version: ranges the `target`-th scan (pre-order) over its
// `<scanPrefix>` relation, and redirects every insert to `<headPrefix><head relation>`. The auxiliary columns
// are preserved (the tuple shape is unchanged). Profile text is dropped (irrelevant to the delta rule).
struct DeltaRewriter : public ram::NodeMapper {
    std::size_t target;
    std::string scanPrefix;
    std::string headPrefix;
    mutable std::size_t scanIdx = 0;
    DeltaRewriter(std::size_t target, std::string scanPrefix, std::string headPrefix)
            : target(target), scanPrefix(std::move(scanPrefix)), headPrefix(std::move(headPrefix)) {}

    Own<ram::Node> operator()(Own<ram::Node> node) const override {
        if (const auto* scan = as<ram::Scan>(node.get())) {
            std::size_t idx = scanIdx++;
            node->apply(*this);  // rewrite nested operations first
            if (idx == target) {
                return mk<ram::Scan>(scanPrefix + scan->getRelation(), scan->getTupleId(),
                        clone(scan->getOperation()), "");
            }
            return node;
        }
        if (const auto* insert = as<ram::Insert>(node.get())) {
            node->apply(*this);
            VecOwn<ram::Expression> values;
            for (const auto* value : insert->getValues()) {
                values.push_back(clone(value));
            }
            return mk<ram::Insert>(headPrefix + insert->getRelation(), std::move(values));
        }
        node->apply(*this);
        return node;
    }
};
}  // namespace

Own<ram::Statement> UnitTranslator::generateDeltaRules(const ast::Relation& rel,
        const std::string& scanPrefix, const std::string& headPrefix, bool includeRecursive) const {
    VecOwn<ram::Statement> result;
    for (auto&& clause : context->getProgram()->getClauses(rel)) {
        if (isA<ast::SubsumptiveClause>(clause)) {
            continue;
        }
        if (!includeRecursive && context->isRecursiveClause(clause)) {
            continue;
        }
        // Translate the clause normally (over the real relations, so the analyses are satisfied), then emit
        // one delta version per scan via a RAM-level relation rename.
        auto base = context->translateNonRecursiveClause(*clause);
        std::size_t numScans = 0;
        visit(*base, [&](const ram::Scan&) { numScans++; });
        for (std::size_t i = 0; i < numScans; i++) {
            auto version = clone(base);
            DeltaRewriter rewriter(i, scanPrefix, headPrefix);
            version->apply(rewriter);
            appendStmt(result, std::move(version));
        }
    }
    return mk<ram::Sequence>(std::move(result));
}

// Erase from `destRelation` every tuple in `srcRelation`, copying all columns (data + the two auxiliary
// columns). The relation keys on the data columns, so the auxiliary values supplied do not affect the match.
Own<ram::Statement> UnitTranslator::generateEraseAll(
        const ast::Relation* rel, const std::string& destRelation, const std::string& srcRelation) const {
    VecOwn<ram::Expression> values;
    for (std::size_t i = 0; i < rel->getArity() + 2; i++) {
        values.push_back(mk<ram::TupleElement>(0, i));
    }
    return mk<ram::Query>(mk<ram::Scan>(srcRelation, 0, mk<ram::Erase>(destRelation, std::move(values))));
}

std::set<std::string> UnitTranslator::stratumDependencies(const ast::RelationSet& scc) const {
    std::set<std::string> sccNames;
    for (const ast::Relation* rel : scc) {
        sccNames.insert(getConcreteRelationName(rel->getQualifiedName()));
    }
    std::set<std::string> deps;
    for (const ast::Relation* rel : scc) {
        for (const auto* clause : context->getProgram()->getClauses(*rel)) {
            visit(*clause, [&](const ast::Atom& atom) {
                std::string name = getConcreteRelationName(atom.getQualifiedName());
                if (sccNames.find(name) == sccNames.end()) {
                    deps.insert(name);
                }
            });
        }
    }
    return deps;
}

Own<ram::Statement> UnitTranslator::guardStratum(
        Own<ram::Statement> body, const std::set<std::string>& signalRelations) const {
    // clean = every signal relation is empty (a dependency's __dirty flag, or an input relation's own staged
    // diff). LOOP { EXIT(clean); <body>; EXIT(true); } runs the body once iff some signal is non-empty.
    Own<ram::Condition> clean = mk<ram::True>();
    for (const auto& name : signalRelations) {
        clean = mk<ram::Conjunction>(std::move(clean), mk<ram::EmptinessCheck>(name));
    }
    VecOwn<ram::Statement> loopBody;
    appendStmt(loopBody, mk<ram::Exit>(std::move(clean)));
    appendStmt(loopBody, std::move(body));
    appendStmt(loopBody, mk<ram::Exit>(mk<ram::True>()));
    return mk<ram::Loop>(mk<ram::Sequence>(std::move(loopBody)));
}

// The signal relations whose non-emptiness means a stratum must run: each dependency's __dirty flag, plus —
// for an input relation in the stratum — its own staged diff (an input change is independent of what it reads).
std::set<std::string> UnitTranslator::stratumSignals(const ast::RelationSet& scc) const {
    std::set<std::string> signals;
    for (const auto& dep : stratumDependencies(scc)) {
        signals.insert("__dirty_" + dep);
    }
    for (const ast::Relation* rel : scc) {
        if (!context->getLoadDirectives(rel->getQualifiedName()).empty()) {
            signals.insert(diffPlusName(rel));
            signals.insert(diffMinusName(rel));
        }
    }
    return signals;
}

Own<ram::Statement> UnitTranslator::generateIncrementalNonRecursive(const ast::Relation& rel) const {
    VecOwn<ram::Statement> result;
    appendStmt(result, generateDeltaRules(rel, "diff_plus_", "diff_plus_", /* includeRecursive */ false));
    // Publish the newly-derived tuples into the full relation.
    appendStmt(result, generateMergeRelations(
                               &rel, getConcreteRelationName(rel.getQualifiedName()), diffPlusName(&rel)));
    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> UnitTranslator::generateIncrementalDelete(const ast::Relation& rel) const {
    // DRed-style deletion for a non-recursive relation:
    //   1. over-delete: the delta rules over diff_minus of dependencies compute the candidate deletions into
    //      diff_minus_<R> (tuples derived using a now-deleted tuple);
    //   2. erase those candidates from <R>;
    //   3. re-derive <R> from the surviving relations — re-adds any candidate that still has support, and is a
    //      no-op (set dedup) for the untouched tuples. Sound for monotone programs.
    VecOwn<ram::Statement> result;
    appendStmt(result, generateDeltaRules(rel, "diff_minus_", "diff_minus_", /* includeRecursive */ false));
    appendStmt(result, generateEraseAll(&rel, getConcreteRelationName(rel.getQualifiedName()),
                               getConcreteRelationName(rel.getQualifiedName(), "diff_minus_")));
    appendStmt(result, generateNonRecursiveRelation(rel));
    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> UnitTranslator::generateSetDirty(const ast::RelationSet& scc) const {
    VecOwn<ram::Statement> result;
    for (const ast::Relation* rel : scc) {
        appendStmt(result, mk<ram::Query>(mk<ram::Insert>(dirtyName(rel), VecOwn<ram::Expression>{})));
    }
    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> UnitTranslator::generateStratumRecompute(
        const ast::RelationSet& scc, std::size_t sccNumber, bool publish) const {
    // Recompute a stratum, correct for insertions, deletions AND negation sign-flips (which add and remove
    // tuples that a from-scratch evaluation simply gets right). Empty each relation (so no-longer-derivable
    // tuples disappear), then re-run the standard evaluation over the already-patched dependencies. Used for
    // recursive monotone strata (a diff-seeded fixpoint can't retract), and for ALL strata of a non-monotone
    // program (negation makes incremental insertion unsound).
    //
    // When `publish` is set, the old contents go to diff_minus and the new contents to diff_plus, so a
    // downstream incremental (monotone) stratum sees the change. A non-monotone program recomputes every
    // stratum, so it does not publish (downstream recomputes from the full relations anyway).
    VecOwn<ram::Statement> result;
    const bool recursive = context->isRecursiveSCC(sccNumber);

    // Empty each relation cheaply: swap its contents into the @swap temp (O(1) btree swap), then bulk-purge
    // the temp. This avoids erasing R tuple by tuple (the dominant cost — erase is O(|R|) costly btree_delete
    // operations). The Swap synthesiser visitor swaps object CONTENTS for exposed relations, so getRelation
    // still sees the right object.
    for (const ast::Relation* rel : scc) {
        const std::string mainName = getConcreteRelationName(rel->getQualifiedName());
        appendStmt(result, mk<ram::Swap>(mainName, swapName(rel)));
        appendStmt(result, mk<ram::Clear>(swapName(rel)));
    }

    // A relation that is BOTH read from input AND has rules holds (input facts ∪ derived facts). Emptying it
    // above dropped its input facts too, so re-apply the staged input from diff_plus before re-deriving. (The
    // driver stages the full input for such relations.)
    for (const ast::Relation* rel : scc) {
        if (!context->getLoadDirectives(rel->getQualifiedName()).empty()) {
            appendStmt(result, generateMergeRelations(
                                       rel, getConcreteRelationName(rel->getQualifiedName()), diffPlusName(rel)));
        }
    }

    // Re-run the standard from-scratch evaluation over the (already-patched) dependencies.
    if (recursive) {
        appendStmt(result, generateRecursiveStratum(scc, sccNumber));
    } else {
        appendStmt(result, generateNonRecursiveRelation(**scc.begin()));
    }

    // Signal that this stratum ran, so downstream guards fire (the cheap dirty signal — replaces copying the
    // whole relation to diff just to mark a change).
    appendStmt(result, generateSetDirty(scc));

    // When publishing, expose the new contents as insertions for downstream incremental strata. (The old
    // contents already sit in diff_minus from the erase scratch above.) Without publishing, the diff_minus
    // scratch is simply left for the driver to purge — no downstream stratum reads it (they recompute from
    // the full relations).
    if (publish) {
        for (const ast::Relation* rel : scc) {
            appendStmt(result, generateMergeRelations(
                                       rel, diffPlusName(rel), getConcreteRelationName(rel->getQualifiedName())));
        }
    }
    return mk<ram::Sequence>(std::move(result));
}

VecOwn<ram::Relation> UnitTranslator::createRamRelations(const std::vector<std::size_t>& sccOrdering) const {
    auto ramRelations = seminaive::UnitTranslator::createRamRelations(sccOrdering);

    // One `diff_plus_<R>` staging relation per relation (same shape, including the auxiliary columns). The
    // driver stages inserted facts here; `update` reads them. Named without an `@` so it is exposed through
    // the program interface for the driver to populate.
    for (auto scc : sccOrdering) {
        for (const ast::Relation* rel : context->getRelationsInSCC(scc)) {
            ramRelations.push_back(createRamRelation(rel, diffPlusName(rel), RelationRepresentation::DEFAULT));
            ramRelations.push_back(createRamRelation(rel, diffMinusName(rel), RelationRepresentation::DEFAULT));
            // @swap_<R>: a temporary of the same shape, for swap-based clearing.
            ramRelations.push_back(createRamRelation(rel, swapName(rel), RelationRepresentation::DEFAULT));
            // __dirty_<R>: a nullary "ran" flag (no auxiliary columns) — the cheap dirty signal.
            ramRelations.push_back(mk<ram::Relation>(dirtyName(rel), 0, 0, std::vector<std::string>{},
                    std::vector<std::string>{}, RelationRepresentation::DEFAULT));
        }
    }
    return ramRelations;
}

std::set<std::size_t> UnitTranslator::computeDeltaEligible(
        const std::vector<std::size_t>& sccOrdering) const {
    const ast::Program* program = context->getProgram();

    // Map every relation's concrete name to its SCC index, so a clause-body dependency name can be resolved to
    // the stratum that produces it.
    std::map<std::string, std::size_t> sccOf;
    for (std::size_t scc : sccOrdering) {
        for (const ast::Relation* rel : context->getRelationsInSCC(scc)) {
            sccOf[getConcreteRelationName(rel->getQualifiedName())] = scc;
        }
    }

    // A stratum is "locally delta-able" iff it is non-recursive and no clause of any of its relations uses
    // negation or an aggregate. (EDB strata have no clauses, so they pass trivially.)
    auto localDeltaable = [&](std::size_t scc) {
        if (context->isRecursiveSCC(scc)) {
            return false;
        }
        bool clean = true;
        for (const ast::Relation* rel : context->getRelationsInSCC(scc)) {
            for (const auto* clause : program->getClauses(*rel)) {
                visit(*clause, [&](const ast::Negation&) { clean = false; });
                visit(*clause, [&](const ast::Aggregator&) { clean = false; });
            }
        }
        return clean;
    };

    // Forward pass in topological order: a stratum is eligible iff it is locally delta-able AND every
    // dependency stratum is already eligible (EDB strata, having no dependencies, become eligible first).
    std::set<std::size_t> eligible;
    for (std::size_t scc : sccOrdering) {
        if (!localDeltaable(scc)) {
            continue;
        }
        bool depsOk = true;
        for (const auto& dep : stratumDependencies(context->getRelationsInSCC(scc))) {
            auto it = sccOf.find(dep);
            if (it == sccOf.end() || eligible.find(it->second) == eligible.end()) {
                depsOk = false;
                break;
            }
        }
        if (depsOk) {
            eligible.insert(scc);
        }
    }
    return eligible;
}

Own<ram::Sequence> UnitTranslator::generateProgram(const ast::TranslationUnit& translationUnit) {
    // Build the normal program first; this also registers the per-stratum subroutines and sets `glb`.
    auto ramProgram = seminaive::UnitTranslator::generateProgram(translationUnit);

    // Register the `update` subroutine: the entry point the driver calls to re-evaluate after an input diff,
    // instead of restarting the process. Its body is INLINED evaluation RAM (a subroutine cannot Call the
    // per-stratum subroutines — those C++ objects are scoped to MAIN).
    //
    // The `update` subroutine handles INSERTIONS. Processing strata in topological order, the input diff
    // propagates through the `diff_plus_<R>` relations:
    //   - extensional R: merge the staged `diff_plus_<R>` into <R>.
    //   - non-recursive intensional R: incremental delta evaluation (only if the program is monotone) —
    //     derive only the tuples that use a newly-inserted fact, into `diff_plus_<R>`, then merge into <R>.
    //   - recursive R: recompute the stratum (the diff-seeded fixpoint is a later step), then conservatively
    //     publish the whole relation into `diff_plus_<R>` so downstream delta evaluation still sees the change.
    // Incremental insertion is only SOUND for monotone (negation-free) programs — with negation, inserting a
    // fact can delete derived tuples. For non-monotone programs the update falls back to merging the staged
    // diff and re-running every stratum (correct for insertion; deletion is a later step). Nothing is cleared
    // (insertion is monotone, and in-subroutine ram::Clear is unreliable: the synthesiser gates an
    // intermediate relation's purge on pruneImdtRels, unset under executeSubroutine). The driver owns the
    // staging relations' lifecycle and purges them after the call.
    const auto& sccOrdering =
            translationUnit.getAnalysis<ast::analysis::TopologicallySortedSCCGraphAnalysis>().order();
    const ast::Program* program = context->getProgram();

    // Monotone = no construct whose result can DECREASE when an input grows. Negation and aggregates both
    // qualify (inserting a fact can falsify a negation or lower/raise an aggregate, retracting derived
    // tuples), so a program using either is recomputed rather than delta-updated.
    bool monotone = true;
    visit(*program, [&](const ast::Negation&) { monotone = false; });
    visit(*program, [&](const ast::Aggregator&) { monotone = false; });

    // Per-stratum delta eligibility: even when the program is non-monotone overall, the strata in the
    // EDB-fed negation/aggregate-free closure can still use the O(diff) delta path (their dependencies all hand
    // them a precise small diff). A globally monotone program has every non-recursive intensional stratum
    // eligible (preserving the original behaviour, including delta downstream of a recursive stratum that
    // publishes); a non-monotone program upgrades just the closure.
    const std::set<std::size_t> deltaEligible = computeDeltaEligible(sccOrdering);

    VecOwn<ram::Statement> body;
    for (std::size_t i = 0; i < sccOrdering.size(); i++) {
        std::size_t scc = sccOrdering.at(i);
        const auto& sccRelations = context->getRelationsInSCC(scc);
        if (context->isRecursiveSCC(scc)) {
            // Recursive strata recompute (a diff-seeded fixpoint can't retract). Publish for a downstream
            // monotone delta stratum only when the program is monotone; the cheap __dirty flag (set inside
            // generateStratumRecompute) carries the selective-stratum signal either way.
            appendStmt(body, guardStratum(generateStratumRecompute(sccRelations, scc, /* publish */ monotone),
                                     stratumSignals(sccRelations)));
        } else if (!sccRelations.empty()) {
            const ast::Relation* rel = *sccRelations.begin();
            if (program->getClauses(*rel).empty()) {
                // Extensional: erase the staged deletions, merge the staged insertions, signal it ran.
                // Guarded on its own staged diff (it has no dependencies).
                VecOwn<ram::Statement> edb;
                appendStmt(edb, generateEraseAll(rel, getConcreteRelationName(rel->getQualifiedName()),
                                       diffMinusName(rel)));
                appendStmt(edb, generateMergeRelations(rel,
                                       getConcreteRelationName(rel->getQualifiedName()), diffPlusName(rel)));
                appendStmt(edb, generateSetDirty(sccRelations));
                appendStmt(body, guardStratum(mk<ram::Sequence>(std::move(edb)),
                                         {diffPlusName(rel), diffMinusName(rel)}));
            } else if (monotone || deltaEligible.count(scc)) {
                // Delta-eligible intensional: deletion (DRed) then insertion (delta); the delta itself
                // populates diff_plus/diff_minus (the precise diff its downstream eligible strata consume), and
                // __dirty signals downstream. Used for every non-recursive intensional stratum of a monotone
                // program, and for the EDB-fed negation/aggregate-free closure of a non-monotone one.
                VecOwn<ram::Statement> idb;
                appendStmt(idb, generateIncrementalDelete(*rel));
                appendStmt(idb, generateIncrementalNonRecursive(*rel));
                appendStmt(idb, generateSetDirty(sccRelations));
                appendStmt(body, guardStratum(mk<ram::Sequence>(std::move(idb)),
                                         stratumSignals(sccRelations)));
            } else {
                // Non-eligible intensional (negation/aggregate in its own clauses, or downstream of a recompute
                // stratum): recompute so sign-flips are retracted correctly (sets __dirty). No eligible stratum
                // depends on it, so it need not publish a precise diff.
                appendStmt(body, guardStratum(generateStratumRecompute(sccRelations, scc, /* publish */ false),
                                         stratumSignals(sccRelations)));
            }
        }
    }

    addRamSubroutine("update", mk<ram::Sequence>(std::move(body)));

    return ramProgram;
}

Own<ram::Relation> UnitTranslator::createRamRelation(const ast::Relation* baseRelation,
        std::string ramRelationName, RelationRepresentation representation) const {
    auto relation =
            seminaive::UnitTranslator::createRamRelation(baseRelation, ramRelationName, representation);

    std::size_t arity = relation->getArity();
    std::size_t auxiliaryArity = relation->getAuxiliaryArity();
    std::vector<std::string> attributeNames = relation->getAttributeNames();
    std::vector<std::string> attributeTypeQualifiers = relation->getAttributeTypes();

    // Sparse-state columns for incremental evaluation.
    attributeNames.push_back("@count");
    attributeTypeQualifiers.push_back("i:number");

    attributeNames.push_back("@iteration");
    attributeTypeQualifiers.push_back("i:number");

    // The incremental update erases tuples (DRed deletion), which the default btree representation does not
    // support — use the deletion-capable btree. Leave non-default representations (e.g. EQREL) untouched.
    if (representation == RelationRepresentation::DEFAULT || representation == RelationRepresentation::BTREE) {
        representation = RelationRepresentation::BTREE_DELETE;
    }

    return mk<ram::Relation>(ramRelationName, arity + 2, auxiliaryArity + 2, attributeNames,
            attributeTypeQualifiers, representation);
}

void UnitTranslator::addAuxiliaryArity(
        const ast::Relation* /* relation */, std::map<std::string, std::string>& directives) const {
    directives.insert(std::make_pair("auxArity", "2"));
}

Own<ram::Statement> UnitTranslator::generateMergeRelations(
        const ast::Relation* rel, const std::string& destRelation, const std::string& srcRelation) const {
    VecOwn<ram::Expression> values;

    // Copy every column, including the two auxiliary columns.
    for (std::size_t i = 0; i < rel->getArity() + 2; i++) {
        values.push_back(mk<ram::TupleElement>(0, i));
    }

    auto insertion = mk<ram::Insert>(destRelation, std::move(values));
    auto stmt = mk<ram::Query>(mk<ram::Scan>(srcRelation, 0, std::move(insertion)));
    if (rel->getRepresentation() == RelationRepresentation::EQREL) {
        return mk<ram::Sequence>(mk<ram::MergeExtend>(destRelation, srcRelation), std::move(stmt));
    }
    return stmt;
}

}  // namespace souffle::ast2ram::incremental
