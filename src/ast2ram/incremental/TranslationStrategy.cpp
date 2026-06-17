/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TranslationStrategy.cpp
 *
 * The elastic incremental evaluation strategy. The unit and clause
 * translators are incremental-specific (they add and thread the
 * @count / @iteration auxiliary columns); the constraint and value
 * translators are inherited from the semi-naive strategy unchanged.
 *
 * With the column VALUES still at their scaffold placeholders, the RAM
 * (and therefore program output) produced under `--incremental` remains
 * identical to the default strategy.
 *
 ***********************************************************************/

#include "ast2ram/incremental/TranslationStrategy.h"
#include "ast2ram/incremental/ClauseTranslator.h"
#include "ast2ram/incremental/ConstraintTranslator.h"
#include "ast2ram/incremental/UnitTranslator.h"
#include "ast2ram/seminaive/ValueTranslator.h"
#include "ast2ram/utility/TranslatorContext.h"
#include "ram/Condition.h"
#include "ram/Expression.h"

namespace souffle::ast2ram::incremental {

ast2ram::UnitTranslator* TranslationStrategy::createUnitTranslator() const {
    return new incremental::UnitTranslator();
}

ast2ram::ClauseTranslator* TranslationStrategy::createClauseTranslator(
        const TranslatorContext& context, TranslationMode mode) const {
    return new incremental::ClauseTranslator(context, mode);
}

ast2ram::ConstraintTranslator* TranslationStrategy::createConstraintTranslator(
        const TranslatorContext& context, const ValueIndex& index) const {
    return new incremental::ConstraintTranslator(context, index);
}

ast2ram::ValueTranslator* TranslationStrategy::createValueTranslator(
        const TranslatorContext& context, const ValueIndex& index) const {
    return new seminaive::ValueTranslator(context, index);
}

}  // namespace souffle::ast2ram::incremental
