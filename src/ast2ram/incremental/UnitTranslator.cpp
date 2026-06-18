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
#include "ram/Erase.h"
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
#include "ram/TupleElement.h"
#include "ram/UnsignedConstant.h"
#include "ram/Variable.h"
#include "ram/utility/Visitor.h"
#include "souffle/utility/ContainerUtil.h"
#include "souffle/utility/MiscUtil.h"
#include <cstddef>
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

Own<ram::Statement> UnitTranslator::generateIncrementalRecursive(
        const ast::RelationSet& scc, std::size_t sccNumber) const {
    // Recompute the recursive stratum, handling insertions AND deletions. A diff-seeded fixpoint propagates
    // insertions cheaply but does not retract tuples that lost support; getting both right inside a fixpoint
    // is recursive DRed with re-discovery (future work). Instead: publish the old contents as deletions
    // (into diff_minus), empty the relation, re-run the standard from-scratch fixpoint over the patched
    // dependencies, then publish the new contents as insertions (into diff_plus). Correct for insert and
    // delete; conservative for any downstream stratum (it sees the whole relation replaced, old->diff_minus
    // and new->diff_plus, which its own update handles).
    VecOwn<ram::Statement> result;

    // Old contents -> diff_minus (publish), then erase to empty the relation.
    for (const ast::Relation* rel : scc) {
        const std::string mainName = getConcreteRelationName(rel->getQualifiedName());
        appendStmt(result, generateMergeRelations(rel, diffMinusName(rel), mainName));
        appendStmt(result, generateEraseAll(rel, mainName, diffMinusName(rel)));
    }

    // Re-run the standard from-scratch recursive stratum over the (already patched) dependencies.
    appendStmt(result, generateRecursiveStratum(scc, sccNumber));

    // New contents -> diff_plus (publish) for downstream strata.
    for (const ast::Relation* rel : scc) {
        appendStmt(result, generateMergeRelations(
                                   rel, diffPlusName(rel), getConcreteRelationName(rel->getQualifiedName())));
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
        }
    }
    return ramRelations;
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

    bool monotone = true;
    visit(*program, [&](const ast::Negation&) { monotone = false; });

    VecOwn<ram::Statement> body;
    for (std::size_t i = 0; i < sccOrdering.size(); i++) {
        std::size_t scc = sccOrdering.at(i);
        const auto& sccRelations = context->getRelationsInSCC(scc);
        if (context->isRecursiveSCC(scc)) {
            if (monotone) {
                appendStmt(body, generateIncrementalRecursive(sccRelations, scc));
            } else {
                appendStmt(body, generateRecursiveStratum(sccRelations, scc));
            }
        } else if (!sccRelations.empty()) {
            const ast::Relation* rel = *sccRelations.begin();
            if (program->getClauses(*rel).empty()) {
                // Extensional: erase the staged deletions, then merge the staged insertions.
                appendStmt(body, generateEraseAll(rel, getConcreteRelationName(rel->getQualifiedName()),
                                         diffMinusName(rel)));
                appendStmt(body, generateMergeRelations(rel,
                                         getConcreteRelationName(rel->getQualifiedName()), diffPlusName(rel)));
            } else if (monotone) {
                // Deletion (DRed) then insertion (delta).
                appendStmt(body, generateIncrementalDelete(*rel));
                appendStmt(body, generateIncrementalNonRecursive(*rel));
            } else {
                appendStmt(body, generateNonRecursiveRelation(*rel));
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
