/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ConstraintTranslator.cpp
 *
 * Implements the incremental constraint translator (see header).
 *
 ***********************************************************************/

#include "ast2ram/incremental/ConstraintTranslator.h"
#include "ast/Atom.h"
#include "ast/Negation.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ast2ram/utility/Utils.h"
#include "ast2ram/utility/ValueIndex.h"
#include "ram/Condition.h"
#include "ram/ExistenceCheck.h"
#include "ram/Expression.h"
#include "ram/Negation.h"
#include "ram/UndefValue.h"

namespace souffle::ast2ram::incremental {

Own<ram::Condition> ConstraintTranslator::translateConstraint(const ast::Literal* lit) {
    assert(lit != nullptr && "literal should be defined");
    return ConstraintTranslator(context, index)(*lit);
}

Own<ram::Condition> ConstraintTranslator::visit_(type_identity<ast::Negation>, const ast::Negation& neg) {
    const auto* atom = neg.getAtom();
    VecOwn<ram::Expression> values;

    for (const auto* arg : atom->getArguments()) {
        values.push_back(context.translateValue(index, arg));
    }

    // @count / @iteration auxiliary columns, left free for the membership test.
    values.push_back(mk<ram::UndefValue>());
    values.push_back(mk<ram::UndefValue>());

    return mk<ram::Negation>(
            mk<ram::ExistenceCheck>(getConcreteRelationName(atom->getQualifiedName()), std::move(values)));
}

}  // namespace souffle::ast2ram::incremental
