/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IncrementalRelations.h
 *
 * Classifies each relation for elastic incremental evaluation. Three buckets:
 *
 *   - extensional : relations with no defining rules (read from input). They
 *                   receive the input diff but are not themselves derived.
 *   - bootstrap   : intensional relations whose stratum (SCC) contains an
 *                   aggregate. Incremental aggregates are an open problem, so
 *                   such strata are always recomputed from scratch (Bootstrap)
 *                   rather than updated in place.
 *   - incremental : every other intensional relation. These are the ones the
 *                   Bootstrap/Update machinery maintains incrementally.
 *
 * This pass only computes the classification; it does not modify the program.
 * Later translation phases query it to decide, per relation, whether to emit
 * the incremental (counting / diff) evaluation or a plain recompute.
 *
 ***********************************************************************/

#pragma once

#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include <iosfwd>
#include <set>

namespace souffle::ast::analysis {

class IncrementalRelationsAnalysis : public Analysis {
public:
    static constexpr const char* name = "incremental-relations";

    IncrementalRelationsAnalysis() : Analysis(name) {}

    void run(const TranslationUnit& translationUnit) override;

    void print(std::ostream& os) const override;

    /** Relations maintained incrementally (intensional, no aggregate in their stratum). */
    bool isIncremental(const Relation* rel) const {
        return incremental.find(rel) != incremental.end();
    }

    /** Intensional relations whose stratum bears an aggregate -> always recomputed. */
    bool isBootstrap(const Relation* rel) const {
        return bootstrap.find(rel) != bootstrap.end();
    }

    /** Relations read from input (no defining rules). */
    bool isExtensional(const Relation* rel) const {
        return extensional.find(rel) != extensional.end();
    }

    const std::set<const Relation*>& getIncrementalRelations() const {
        return incremental;
    }
    const std::set<const Relation*>& getBootstrapRelations() const {
        return bootstrap;
    }
    const std::set<const Relation*>& getExtensionalRelations() const {
        return extensional;
    }

private:
    std::set<const Relation*> incremental;
    std::set<const Relation*> bootstrap;
    std::set<const Relation*> extensional;
};

}  // namespace souffle::ast::analysis
