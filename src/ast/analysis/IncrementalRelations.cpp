/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2026 The Souffle Developers. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file IncrementalRelations.cpp
 *
 * Implements the incremental-relation classification (see header).
 *
 ***********************************************************************/

#include "ast/analysis/IncrementalRelations.h"
#include "ast/Aggregator.h"
#include "ast/Clause.h"
#include "ast/Program.h"
#include "ast/Relation.h"
#include "ast/TranslationUnit.h"
#include "ast/analysis/SCCGraph.h"
#include "ast/utility/Visitor.h"
#include <cstddef>
#include <ostream>
#include <set>
#include <vector>

namespace souffle::ast::analysis {

void IncrementalRelationsAnalysis::run(const TranslationUnit& translationUnit) {
    const Program& program = translationUnit.getProgram();
    const auto& sccGraph = translationUnit.getAnalysis<SCCGraphAnalysis>();

    // A stratum (SCC) is "bootstrap" if any relation it contains is defined by a
    // clause that uses an aggregate. Such strata are recomputed wholesale rather
    // than maintained incrementally (incremental aggregation is not supported).
    const std::size_t numSCCs = sccGraph.getNumberOfSCCs();
    std::set<std::size_t> aggregateSCCs;
    for (std::size_t scc = 0; scc < numSCCs; ++scc) {
        for (const Relation* rel : sccGraph.getInternalRelations(scc)) {
            for (const Clause* clause : program.getClauses(*rel)) {
                bool found = false;
                visit(*clause, [&](const Aggregator&) { found = true; });
                if (found) {
                    aggregateSCCs.insert(scc);
                    break;
                }
            }
            if (aggregateSCCs.count(scc) != 0u) {
                break;
            }
        }
    }

    for (const Relation* rel : program.getRelations()) {
        // No defining rules -> extensional (read from input, not derived).
        if (program.getClauses(*rel).empty()) {
            extensional.insert(rel);
            continue;
        }
        // Intensional: incremental unless its stratum bears an aggregate.
        if (aggregateSCCs.count(sccGraph.getSCC(rel)) != 0u) {
            bootstrap.insert(rel);
        } else {
            incremental.insert(rel);
        }
    }
}

void IncrementalRelationsAnalysis::print(std::ostream& os) const {
    auto printBucket = [&os](const char* label, const std::set<const Relation*>& rels) {
        os << label << " (" << rels.size() << "):\n";
        for (const Relation* rel : rels) {
            os << "  " << rel->getQualifiedName() << "\n";
        }
    };
    os << "-- incremental relation classification --\n";
    printBucket("incremental", incremental);
    printBucket("bootstrap (aggregate stratum)", bootstrap);
    printBucket("extensional (input)", extensional);
}

}  // namespace souffle::ast::analysis
