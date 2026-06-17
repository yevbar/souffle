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

        // Bind this atom's two auxiliary columns so they can be threaded.
        valueIndex->addVarReference("@count_" + std::to_string(atomIdx), scanLevel, atom->getArity());
        valueIndex->addVarReference("@iteration_" + std::to_string(atomIdx), scanLevel, atom->getArity() + 1);

        atomIdx++;
    }
}

Own<ram::Expression> ClauseTranslator::getIterationNumber(const ast::Clause& clause) const {
    const auto& bodyAtoms = getAtomOrdering(clause);
    if (bodyAtoms.empty()) return mk<ram::SignedConstant>(0);

    VecOwn<ram::Expression> depths;
    for (std::size_t i = 0; i < bodyAtoms.size(); i++) {
        auto iterVar = mk<ast::Variable>("@iteration_" + std::to_string(i));
        depths.push_back(context.translateValue(*valueIndex, iterVar.get()));
    }

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
    values.push_back(mk<ram::UndefValue>());  // @count: free
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

    // @count is a placeholder (1) until multiset accounting lands. @iteration
    // is the derivation depth: one more than the deepest body atom (0 for a
    // fact). Set semantics keeps the first derivation, so this records the
    // depth at which the tuple first appears.
    values.push_back(mk<ram::SignedConstant>(1));        // @count
    values.push_back(getIterationNumber(clause));        // @iteration

    // Propositions
    if (head->getArity() == 0) {
        return mk<ram::Filter>(
                mk<ram::EmptinessCheck>(headRelationName), mk<ram::Insert>(headRelationName, std::move(values)));
    }

    // Relations with functional dependency constraints
    if (auto guardedConditions = getFunctionalDependencies(clause)) {
        return mk<ram::GuardedInsert>(headRelationName, std::move(values), std::move(guardedConditions));
    }

    // Everything else
    return mk<ram::Insert>(headRelationName, std::move(values));
}

}  // namespace souffle::ast2ram::incremental
