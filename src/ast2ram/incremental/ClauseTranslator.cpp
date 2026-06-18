/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ClauseTranslator.cpp
 *
 * Implements the incremental clause translator (see header).
 *
 ***********************************************************************/

#include "ast2ram/incremental/ClauseTranslator.h"
#include "ast/Atom.h"
#include "ast/Clause.h"
#include "ast/Variable.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ram/EmptinessCheck.h"
#include "ram/ExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Filter.h"
#include "ram/GuardedInsert.h"
#include "ram/Insert.h"
#include "ram/IntrinsicOperator.h"
#include "ram/Negation.h"
#include "ram/Operation.h"
#include "ram/SignedConstant.h"
#include "ram/UndefValue.h"
#include "souffle/utility/ContainerUtil.h"
#include <cstddef>
#include <string>

namespace souffle::ast2ram::incremental {

void ClauseTranslator::indexAtoms(const ast::Clause& clause) {
    std::size_t atomIdx = 0;
    for (const auto* atom : getAtomOrdering(clause)) {
        std::size_t scanLevel = addOperatorLevel(atom);
        indexNodeArguments(scanLevel, atom->getArguments());

        // Bind this atom's single auxiliary column (@iteration, at the position just past the data columns).
        valueIndex->addVarReference("@iteration_" + std::to_string(atomIdx), scanLevel, atom->getArity());

        atomIdx++;
    }
}

Own<ram::Expression> ClauseTranslator::getIterationNumber(const ast::Clause& clause) const {
    const auto& bodyAtoms = getAtomOrdering(clause);

    // Only SCANNED atoms bind an @iteration tuple element. A nullary body atom (a proposition) becomes an
    // existence check, not a scan, so its @iteration_i variable is never bound — reading it produces an
    // undeclared tuple in the generated code. Skip nullary atoms here; their derivation depth does not
    // contribute a readable value.
    VecOwn<ram::Expression> depths;
    for (std::size_t i = 0; i < bodyAtoms.size(); i++) {
        if (bodyAtoms.at(i)->getArity() == 0) {
            continue;
        }
        auto iterVar = mk<ast::Variable>("@iteration_" + std::to_string(i));
        depths.push_back(context.translateValue(*valueIndex, iterVar.get()));
    }
    if (depths.empty()) return mk<ram::SignedConstant>(0);

    auto maxDepth = depths.size() == 1 ? std::move(depths.at(0))
                                       : mk<ram::IntrinsicOperator>(FunctorOp::MAX, std::move(depths));

    VecOwn<ram::Expression> addArgs;
    addArgs.push_back(std::move(maxDepth));
    addArgs.push_back(mk<ram::SignedConstant>(1));
    return mk<ram::IntrinsicOperator>(FunctorOp::ADD, std::move(addArgs));
}

namespace {
// A data-tuple membership test against a relation carrying the two auxiliary
// columns. The data columns are matched by equality; the @count / @iteration
// columns are supplied as free (undef) so the check tests data membership only.
// The auxiliary values must be supplied explicitly: an existence check given
// only the data values is rewritten by index selection into one that ignores
// the auxiliary columns and never matches.
Own<ram::Operation> negatedMembership(Own<ram::Operation> op, std::string relName, const ast::Atom* atom,
        const TranslatorContext& context, const ValueIndex& valueIndex) {
    if (atom->getArity() == 0) {
        // for a nullary, negation is a simple emptiness check
        return mk<ram::Filter>(mk<ram::EmptinessCheck>(relName), std::move(op));
    }

    VecOwn<ram::Expression> values;
    for (const auto* arg : atom->getArguments()) {
        values.push_back(context.translateValue(valueIndex, arg));
    }
    values.push_back(mk<ram::UndefValue>());  // @iteration: free

    return mk<ram::Filter>(
            mk<ram::Negation>(mk<ram::ExistenceCheck>(relName, std::move(values))), std::move(op));
}
}  // namespace

Own<ram::Operation> ClauseTranslator::addNegatedDeltaAtom(
        Own<ram::Operation> op, const ast::Atom* atom) const {
    return negatedMembership(
            std::move(op), getDeltaRelationName(atom->getQualifiedName()), atom, context, *valueIndex);
}

Own<ram::Operation> ClauseTranslator::addNegatedAtom(
        Own<ram::Operation> op, const ast::Clause& /* clause */, const ast::Atom* atom) const {
    return negatedMembership(
            std::move(op), getConcreteRelationName(atom->getQualifiedName()), atom, context, *valueIndex);
}

Own<ram::Operation> ClauseTranslator::createInsertion(const ast::Clause& clause) const {
    const auto head = clause.getHead();
    auto headRelationName = getClauseAtomName(clause, head);

    VecOwn<ram::Expression> values;
    for (const auto* arg : head->getArguments()) {
        values.push_back(context.translateValue(*valueIndex, arg));
    }

    // @iteration is the derivation depth: one more than the deepest body atom (0 for a fact). Set semantics
    // keeps the first derivation, so this records the depth at which the tuple first appears.
    //
    // A nullary (proposition) head uses a CONSTANT iteration: souffle hoists the insert of a nullary relation
    // out of the body scan (it is loop-invariant once derived), so a body-dependent value would reference an
    // out-of-scope tuple. @iteration is internal, stripped state, so the exact depth here does not matter.
    values.push_back(head->getArity() == 0 ? mk<ram::Expression, ram::SignedConstant>(0)
                                           : getIterationNumber(clause));  // @iteration

    // NB: unlike the semi-naive translator we do NOT wrap a nullary (proposition) head in
    // Filter(EmptinessCheck, Insert). That guard is loop-invariant, so the RAM optimiser hoists the nested
    // Insert out of the body scan — but our @iteration value reads a body tuple (env0), which is then out of
    // scope and the generated C++ fails to compile. Inserting directly (the body scan still encloses it) is
    // correct: set semantics dedups the proposition, and the auxiliary columns are stripped from output.

    // Relations with functional dependency constraints
    if (auto guardedConditions = getFunctionalDependencies(clause)) {
        return mk<ram::GuardedInsert>(headRelationName, std::move(values), std::move(guardedConditions));
    }

    // Everything else
    return mk<ram::Insert>(headRelationName, std::move(values));
}

}  // namespace souffle::ast2ram::incremental
