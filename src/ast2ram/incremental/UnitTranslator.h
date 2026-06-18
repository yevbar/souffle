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
     * Emit the delta rules for one relation: for each clause and each scan, a version that ranges that scan
     * over its `diff_plus` and redirects the head insert to `<headPrefix><R>` (a RAM-level relation rename).
     * The union over scans is the derivations using at least one newly-inserted tuple. `includeRecursive`
     * controls whether recursive clauses are included (true when seeding a recursive stratum's @delta).
     */
    Own<ram::Statement> generateDeltaRules(const ast::Relation& rel, const std::string& scanPrefix,
            const std::string& headPrefix, bool includeRecursive) const;

    /** Erase every tuple of `srcRelation` (all columns incl. auxiliary) from `destRelation`. */
    Own<ram::Statement> generateEraseAll(
            const ast::Relation* rel, const std::string& destRelation, const std::string& srcRelation) const;

    /**
     * Wrap a stratum's update in a guard that skips it when none of `dependencies` changed (all their
     * diff_plus / diff_minus are empty) — selective-stratum evaluation. A stratum that runs populates its
     * own diff (the erase scratch / publish), which makes downstream guards fire; a skipped stratum leaves
     * its diff empty, so strata that are not downstream of a change are skipped entirely.
     */
    Own<ram::Statement> guardStratum(
            Own<ram::Statement> body, const std::set<std::string>& dependencies) const;

    /** The relation names a stratum reads in its clause bodies (positive and negated), excluding its own SCC. */
    std::set<std::string> stratumDependencies(const ast::RelationSet& scc) const;

    /**
     * Incremental delta evaluation of a non-recursive relation: the delta rules into `diff_plus_<R>`, then
     * merge into <R>. Only sound for monotone programs.
     */
    Own<ram::Statement> generateIncrementalNonRecursive(const ast::Relation& rel) const;

    /**
     * DRed-style incremental deletion of a non-recursive relation: over-delete candidates into
     * `diff_minus_<R>`, erase them from <R>, then re-derive from the survivors. Only sound for monotone
     * programs.
     */
    Own<ram::Statement> generateIncrementalDelete(const ast::Relation& rel) const;

    /**
     * Recompute a stratum from scratch — empty its relations, then re-run the standard evaluation over the
     * patched dependencies. Correct for insertions, deletions and negation sign-flips. Used for recursive
     * strata (a diff-seeded fixpoint can't retract) and for every stratum of a non-monotone program. When
     * `publish` is set, the old contents go to diff_minus and the new to diff_plus for downstream incremental
     * strata.
     */
    Own<ram::Statement> generateStratumRecompute(
            const ast::RelationSet& scc, std::size_t sccNumber, bool publish) const;

    /** Report the two auxiliary columns to the IO directives so they are stripped on write. */
    void addAuxiliaryArity(
            const ast::Relation* relation, std::map<std::string, std::string>& directives) const override;

    /** Copy the auxiliary columns through when merging @new/@delta into the full relation. */
    Own<ram::Statement> generateMergeRelations(const ast::Relation* rel, const std::string& destRelation,
            const std::string& srcRelation) const override;
};

}  // namespace souffle::ast2ram::incremental
