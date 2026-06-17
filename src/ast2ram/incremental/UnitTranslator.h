/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file UnitTranslator.h
 *
 * Unit translator for elastic incremental evaluation. Extends the
 * semi-naive translator so that every relation carries two auxiliary
 * columns, @count (derivation count) and @iteration (the iteration a tuple
 * was first derived in). These are the sparse computational state the
 * incremental Update step reads.
 *
 * Auxiliary columns are excluded from a relation's key and stripped from
 * its emitted output (auxArity), so a program compiled this way produces
 * output identical to the default strategy. The column VALUES are presently
 * placeholders (see ClauseTranslator); the counting evaluation that fills
 * them in is added on top of this scaffold.
 *
 ***********************************************************************/

#pragma once

#include "RelationTag.h"
#include "ast2ram/seminaive/UnitTranslator.h"
#include <map>
#include <string>

namespace souffle::ast {
class Relation;
class TranslationUnit;
}  // namespace souffle::ast

namespace souffle::ram {
class Relation;
class Sequence;
class Statement;
}  // namespace souffle::ram

namespace souffle::ast2ram::incremental {

class UnitTranslator : public ast2ram::seminaive::UnitTranslator {
public:
    UnitTranslator() : ast2ram::seminaive::UnitTranslator() {}

protected:
    /** Generate the normal program, then register the incremental `update` subroutine. */
    Own<ram::Sequence> generateProgram(const ast::TranslationUnit& translationUnit) override;

    /** Create the normal relations plus a `diff_plus_<R>` staging relation per relation. */
    VecOwn<ram::Relation> createRamRelations(const std::vector<std::size_t>& sccOrdering) const override;

    /** Grow every relation by the @count / @iteration auxiliary columns. */
    Own<ram::Relation> createRamRelation(const ast::Relation* baseRelation, std::string ramRelationName,
            RelationRepresentation) const override;

private:
    /**
     * Incremental delta evaluation of a non-recursive relation. Each clause is translated normally, then for
     * each scan a version is emitted that ranges that one scan over its `diff_plus` and inserts into
     * `diff_plus_<R>` (a RAM-level relation-name rewrite). The union over scans is exactly the derivations
     * using at least one newly-inserted tuple. Finally `diff_plus_<R>` is merged into <R>. Only sound for
     * monotone programs, so the caller gates it on the absence of negation.
     */
    Own<ram::Statement> generateIncrementalNonRecursive(const ast::Relation& rel) const;

    /** Report the two auxiliary columns to the IO directives so they are stripped on write. */
    void addAuxiliaryArity(
            const ast::Relation* relation, std::map<std::string, std::string>& directives) const override;

    /** Copy the auxiliary columns through when merging @new/@delta into the full relation. */
    Own<ram::Statement> generateMergeRelations(const ast::Relation* rel, const std::string& destRelation,
            const std::string& srcRelation) const override;
};

}  // namespace souffle::ast2ram::incremental
