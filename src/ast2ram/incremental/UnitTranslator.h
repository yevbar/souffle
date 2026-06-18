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

    /** The signal relations whose non-emptiness means the stratum must run (dep __dirty flags + own input diff). */
    std::set<std::string> stratumSignals(const ast::RelationSet& scc) const;

    /** Set the nullary `__dirty_<R>` "ran" flag for each relation in the stratum (the cheap dirty signal). */
    Own<ram::Statement> generateSetDirty(const ast::RelationSet& scc) const;

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

    /**
     * The set of SCC indices that may use the O(diff) delta path instead of an O(|R|) recompute, even in a
     * non-monotone program. A stratum is delta-eligible iff it is non-recursive, its own clauses contain no
     * negation and no aggregate (the delta machinery rewrites scans, not existence checks or aggregates), and
     * every dependency hands it a precise small diff — i.e. each dependency is an EDB input or itself lies in a
     * delta-eligible stratum. This is a closure over the stratum DAG, computed by a forward pass over the
     * topological `sccOrdering` (dependencies precede dependents). EDB strata (no clauses, no dependencies) are
     * trivially eligible — they publish their staged diff.
     */
    std::set<std::size_t> computeDeltaEligible(const std::vector<std::size_t>& sccOrdering) const;

    /**
     * Re-derive ONLY the over-deleted candidates (the tuples in `diff_minus_<rel>`), not the whole relation.
     * Each non-recursive clause is translated normally, then its head Insert is wrapped in a membership test
     * against `diff_minus_<rel>` so a tuple is re-added iff it was a deletion candidate AND still has support.
     * This is the DRed re-derivation restricted to candidates — O(|diff_minus|·body) instead of O(|rel|·body),
     * and a no-op when there are no deletions (insertion-only updates), making the delta path truly O(diff).
     */
    Own<ram::Statement> generateRederiveCandidates(const ast::Relation& rel) const;

    /**
     * Negation-delta OVER-DELETION: for each negated body atom `!N`, emit a delta rule that ranges that atom
     * over `diff_plus_<N>` (the tuples N just gained) instead of checking `!N`, with the head Insert redirected
     * to `diff_minus_<H>`. A head tuple whose positive body still holds but whose negated atom just became true
     * is no longer supported via that clause — an over-deletion candidate (the candidate-restricted re-derive
     * then keeps any with an alternative support). One version per negated atom; a no-op for neg-free clauses.
     */
    Own<ram::Statement> generateNegationOverDelete(const ast::Relation& rel) const;

    /**
     * Negation-delta INSERTION: for each negated body atom `!N`, emit a delta rule that keeps the `!N` check
     * (true now) AND additionally requires the atom in `diff_minus_<N>` (the tuples N just lost), with the head
     * Insert redirected to `diff_plus_<H>`. A head tuple becomes newly derivable when a blocking negated atom is
     * removed. One version per negated atom; a no-op for neg-free clauses.
     */
    Own<ram::Statement> generateNegationInsert(const ast::Relation& rel) const;

    /** Report the two auxiliary columns to the IO directives so they are stripped on write. */
    void addAuxiliaryArity(
            const ast::Relation* relation, std::map<std::string, std::string>& directives) const override;

    /** Copy the auxiliary columns through when merging @new/@delta into the full relation. */
    Own<ram::Statement> generateMergeRelations(const ast::Relation* rel, const std::string& destRelation,
            const std::string& srcRelation) const override;

    /**
     * The concrete names of the MAIN relations that the `update` actually erases (`ram::Erase`) — exactly the
     * EDB relations and the delta-eligible intensional relations. Only these need the deletion-capable
     * `BTREE_DELETE` representation; everything else (recompute-stratum mains, which swap-clear; and all the
     * diff_plus_/diff_minus_/@swap_ relations, which are scanned/purged/merged but never erased) keeps the fast
     * btree. Populated in createRamRelations before the relations are built, read by createRamRelation.
     */
    mutable std::set<std::string> erasedRelations;
};

}  // namespace souffle::ast2ram::incremental
