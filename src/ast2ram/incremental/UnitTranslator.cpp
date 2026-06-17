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
// The staging relation that holds tuples inserted into <R> for the next update.
std::string diffPlusName(const ast::Relation* rel) {
    return getConcreteRelationName(rel->getQualifiedName(), "diff_plus_");
}

// Rewrites one clause's RAM into a delta version: ranges the `target`-th scan (pre-order) over its diff_plus
// relation, and redirects every insert to `<headPrefix><head relation>`. The auxiliary columns are preserved
// (the tuple shape is unchanged). Profile text is dropped (irrelevant to the delta rule).
struct DeltaRewriter : public ram::NodeMapper {
    std::size_t target;
    std::string headPrefix;
    mutable std::size_t scanIdx = 0;
    DeltaRewriter(std::size_t target, std::string headPrefix)
            : target(target), headPrefix(std::move(headPrefix)) {}

    Own<ram::Node> operator()(Own<ram::Node> node) const override {
        if (const auto* scan = as<ram::Scan>(node.get())) {
            std::size_t idx = scanIdx++;
            node->apply(*this);  // rewrite nested operations first
            if (idx == target) {
                return mk<ram::Scan>("diff_plus_" + scan->getRelation(), scan->getTupleId(),
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

Own<ram::Statement> UnitTranslator::generateDeltaRules(
        const ast::Relation& rel, const std::string& headPrefix, bool includeRecursive) const {
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
            DeltaRewriter rewriter(i, headPrefix);
            version->apply(rewriter);
            appendStmt(result, std::move(version));
        }
    }
    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> UnitTranslator::generateIncrementalNonRecursive(const ast::Relation& rel) const {
    VecOwn<ram::Statement> result;
    appendStmt(result, generateDeltaRules(rel, "diff_plus_", /* includeRecursive */ false));
    // Publish the newly-derived tuples into the full relation.
    appendStmt(result, generateMergeRelations(
                               &rel, getConcreteRelationName(rel.getQualifiedName()), diffPlusName(&rel)));
    return mk<ram::Sequence>(std::move(result));
}

Own<ram::Statement> UnitTranslator::generateIncrementalRecursive(
        const ast::RelationSet& scc, std::size_t sccNumber) const {
    VecOwn<ram::Statement> result;

    // Seed each relation's @delta with the new tuples (delta rules using diff_plus of lower-stratum atoms;
    // the version that ranges a same-SCC atom over its empty diff_plus is a harmless no-op), then merge the
    // seed into the full relation.
    for (const ast::Relation* rel : scc) {
        appendStmt(result, generateDeltaRules(*rel, "@delta_", /* includeRecursive */ true));
    }
    for (const ast::Relation* rel : scc) {
        appendStmt(result, generateMergeRelations(rel, getConcreteRelationName(rel->getQualifiedName()),
                                   getDeltaRelationName(rel->getQualifiedName())));
    }

    // The standard semi-naive fixpoint (mirrors generateRecursiveStratum, minus the from-scratch preamble) —
    // driven by the seeded @delta, so the work is proportional to the seed.
    auto joinSizeSequence = mk<ram::Sequence>(context->getRecursiveJoinSizeStatementsInSCC(sccNumber));
    const std::string loopCounter = "loop_counter";
    VecOwn<ram::Expression> inc;
    inc.push_back(mk<ram::Variable>(loopCounter));
    inc.push_back(mk<ram::UnsignedConstant>(1));
    auto incrementCounter = mk<ram::Assign>(mk<ram::Variable>(loopCounter),
            mk<ram::IntrinsicOperator>(FunctorOp::UADD, std::move(inc)), false);
    auto fixpointLoop = mk<ram::Loop>(mk<ram::Sequence>(generateStratumLoopBody(scc),
            std::move(joinSizeSequence), generateStratumExitSequence(scc), generateStratumTableUpdates(scc),
            std::move(incrementCounter)));
    appendStmt(result, mk<ram::Assign>(mk<ram::Variable>(loopCounter), mk<ram::UnsignedConstant>(1), true));
    appendStmt(result, std::move(fixpointLoop));
    appendStmt(result, generateStratumPostamble(scc));

    // Conservatively publish the relations into their diff_plus so downstream strata see the changes.
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
                appendStmt(body, generateMergeRelations(rel,
                                         getConcreteRelationName(rel->getQualifiedName()), diffPlusName(rel)));
            } else if (monotone) {
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
