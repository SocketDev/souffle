/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ResolveAnonymousRecordAliases.cpp
 *
 ***********************************************************************/

#include "ast/transform/ResolveAnonymousRecordAliases.h"
#include "ast/Argument.h"
#include "ast/BinaryConstraint.h"
#include "ast/BooleanConstraint.h"
#include "ast/Clause.h"
#include "ast/Literal.h"
#include "ast/Node.h"
#include "ast/Program.h"
#include "ast/RecordInit.h"
#include "ast/TranslationUnit.h"
#include "ast/UnnamedVariable.h"
#include "ast/Variable.h"
#include "ast/analysis/Ground.h"
#include "ast/analysis/Type.h"
#include "ast/analysis/TypeSystem.h"
#include "ast/utility/NodeMapper.h"
#include "souffle/BinaryConstraintOps.h"
#include "souffle/utility/MiscUtil.h"
#include <map>
#include <memory>
#include <utility>
#include <vector>

namespace souffle::ast::transform {

std::map<std::string, const RecordInit*> ResolveAnonymousRecordAliases::findVariablesRecordMapping(
        TranslationUnit& tu, const Clause& clause) {
    std::map<std::string, const RecordInit*> variableRecordMap;

    auto isVariable = [](Node* node) -> bool { return isA<ast::Variable>(node); };
    auto isRecord = [](Node* node) -> bool { return isA<RecordInit>(node); };

    auto& typeAnalysis = *tu.getAnalysis<analysis::TypeAnalysis>();
    auto groundedTerms = analysis::getGroundedTerms(tu, clause);

    for (auto* literal : clause.getBodyLiterals()) {
        if (auto constraint = dynamic_cast<BinaryConstraint*>(literal)) {
            if (!isEqConstraint(constraint->getOperator())) {
                continue;
            }

            auto left = constraint->getLHS();
            auto right = constraint->getRHS();

            if (!isVariable(left) && !isVariable(right)) {
                continue;
            }

            if (!isRecord(left) && !isRecord(right)) {
                continue;
            }

            // TODO (darth_tytus): This should change in the future.
            // Currently type system assigns to anonymous records {- All types - }
            // which is inelegant.
            if (!typeAnalysis.getTypes(left).isAll()) {
                continue;
            }

            auto* variable = static_cast<ast::Variable*>(isVariable(left) ? left : right);
            const auto& variableName = variable->getName();

            if (!groundedTerms.find(variable)->second) {
                continue;
            }

            // We are interested only in the first mapping.
            if (variableRecordMap.find(variableName) != variableRecordMap.end()) {
                continue;
            }

            auto* record = static_cast<RecordInit*>(isRecord(left) ? left : right);

            variableRecordMap.insert({variableName, record});
        }
    }

    return variableRecordMap;
}

bool ResolveAnonymousRecordAliases::replaceNamedVariables(TranslationUnit& tu, Clause& clause) {
    struct ReplaceVariables : public NodeMapper {
        std::map<std::string, const RecordInit*> varToRecordMap;

        ReplaceVariables(std::map<std::string, const RecordInit*> varToRecordMap)
                : varToRecordMap(std::move(varToRecordMap)){};

        Own<Node> operator()(Own<Node> node) const override {
            if (auto variable = dynamic_cast<ast::Variable*>(node.get())) {
                auto iteratorToRecord = varToRecordMap.find(variable->getName());
                if (iteratorToRecord != varToRecordMap.end()) {
                    return souffle::clone(iteratorToRecord->second);
                }
            }

            node->apply(*this);

            return node;
        }
    };

    auto variableToRecordMap = findVariablesRecordMapping(tu, clause);
    bool changed = variableToRecordMap.size() > 0;
    if (changed) {
        ReplaceVariables update(std::move(variableToRecordMap));
        clause.apply(update);
    }
    return changed;
}

bool ResolveAnonymousRecordAliases::replaceUnnamedVariable(Clause& clause) {
    struct ReplaceUnnamed : public NodeMapper {
        mutable bool changed{false};
        ReplaceUnnamed() = default;

        Own<Node> operator()(Own<Node> node) const override {
            auto isUnnamed = [](Node* node) -> bool { return isA<UnnamedVariable>(node); };
            auto isRecord = [](Node* node) -> bool { return isA<RecordInit>(node); };

            if (auto constraint = dynamic_cast<BinaryConstraint*>(node.get())) {
                auto left = constraint->getLHS();
                auto right = constraint->getRHS();
                bool hasUnnamed = isUnnamed(left) || isUnnamed(right);
                bool hasRecord = isRecord(left) || isRecord(right);
                auto op = constraint->getOperator();
                if (hasUnnamed && hasRecord && isEqConstraint(op)) {
                    return mk<BooleanConstraint>(true);
                }
            }

            node->apply(*this);

            return node;
        }
    };

    ReplaceUnnamed update;
    clause.apply(update);

    return update.changed;
}

bool ResolveAnonymousRecordAliases::transform(TranslationUnit& translationUnit) {
    bool changed = false;
    for (auto* clause : translationUnit.getProgram()->getClauses()) {
        changed |= replaceNamedVariables(translationUnit, *clause);
        changed |= replaceUnnamedVariable(*clause);
    }

    return changed;
}

}  // namespace souffle::ast::transform
