# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

import logging
import string_utils.validation as StringValidation
from af_lint_rule import AsFigoLintRule

class VarNamingConsistencyRule(AsFigoLintRule):
    """Checks for mixed CamelCase and snake_case in variable names."""

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for classNode in data.tree.iter_find_all({"tag": "kClassDeclaration"}):
            className = self.getClassName(classNode)

            numCamelCase = 0
            numSnakeCase = 0

            for varNode in classNode.iter_find_all({"tag": "kDataDeclaration"}):
                for identifier in varNode.iter_find_all({"tag": "SymbolIdentifier"}):
                    varName = identifier.text
                    numCamelCase += int(StringValidation.is_camel_case(varName))
                    numSnakeCase += int(StringValidation.is_snake_case(varName))

            if numCamelCase > 0 and numSnakeCase > 0:
                message = (
                    f"Error: Inconsistent mix of CamelCase and snake_case in class {className}\n"
                    f"CamelCase: {numCamelCase}, snake_case: {numSnakeCase}"
                )
                self.linter.logViolation("R102", message)
