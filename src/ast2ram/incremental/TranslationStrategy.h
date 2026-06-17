/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file TranslationStrategy.h
 *
 * Implementation of an elastic incremental evaluation strategy (Bootstrap /
 * Update, in the style of Zhao et al., PPDP'21). This is currently a SCAFFOLD:
 * it delegates to the semi-naive translators, so `--incremental` is output-
 * identical to the default strategy. The incremental Bootstrap/Update
 * translators (relation annotation, diff_plus/diff_minus, re-discovery) will
 * replace these one factory at a time, each change gated by output parity
 * against this baseline.
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/TranslationStrategy.h"
#include "souffle/utility/ContainerUtil.h"

namespace souffle::ast2ram {
class ClauseTranslator;
class ConstraintTranslator;
class UnitTranslator;
class TranslatorContext;
class ValueIndex;
class ValueTranslator;
}  // namespace souffle::ast2ram

namespace souffle::ast2ram::incremental {

class TranslationStrategy : public ast2ram::TranslationStrategy {
public:
    std::string getName() const override {
        return "IncrementalEvaluation";
    }

    ast2ram::UnitTranslator* createUnitTranslator() const override;
    ast2ram::ClauseTranslator* createClauseTranslator(
            const TranslatorContext& context, TranslationMode mode) const override;
    ast2ram::ConstraintTranslator* createConstraintTranslator(
            const TranslatorContext& context, const ValueIndex& index) const override;
    ast2ram::ValueTranslator* createValueTranslator(
            const TranslatorContext& context, const ValueIndex& index) const override;
};

}  // namespace souffle::ast2ram::incremental
