/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ClauseTranslator.h
 *
 * Clause translator for elastic incremental evaluation. Threads the two
 * auxiliary columns (@count, @iteration) that incremental::UnitTranslator
 * adds to every relation through the operations that touch them: the head
 * insertion appends the two values, and negated body atoms test data-tuple
 * membership with the auxiliary columns left free. Everything else is
 * inherited from the semi-naive translator unchanged.
 *
 * The appended values are placeholders for now — @count = 1, @iteration = 0
 * — chosen so the auxiliary columns are well-formed without yet changing
 * what the program computes. The counting evaluation that gives them their
 * real meaning is layered on top of this scaffold.
 *
 * A negated body atom must supply a value for every column (the data values
 * plus a free value per auxiliary column); an existence check given only the
 * data values is rewritten by index selection into one that ignores the
 * auxiliary columns and never matches. User-written negations are handled the
 * same way by incremental::ConstraintTranslator.
 *
 ***********************************************************************/

#pragma once

#include "ast2ram/seminaive/ClauseTranslator.h"

namespace souffle::ast {
class Atom;
class Clause;
}  // namespace souffle::ast

namespace souffle::ram {
class Operation;
}

namespace souffle::ast2ram {
class TranslatorContext;
}

namespace souffle::ast2ram::incremental {

class ClauseTranslator : public ast2ram::seminaive::ClauseTranslator {
public:
    ClauseTranslator(const TranslatorContext& context, TranslationMode mode = DEFAULT)
            : ast2ram::seminaive::ClauseTranslator(context, mode) {}

protected:
    Own<ram::Operation> addNegatedDeltaAtom(Own<ram::Operation> op, const ast::Atom* atom) const override;
    Own<ram::Operation> addNegatedAtom(
            Own<ram::Operation> op, const ast::Clause& clause, const ast::Atom* atom) const override;
    Own<ram::Operation> createInsertion(const ast::Clause& clause) const override;
};

}  // namespace souffle::ast2ram::incremental
