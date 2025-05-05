# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from af_lint_rule import AsFigoLintRule
import logging

class EncapsulationRule(AsFigoLintRule):
    """Ensures proper encapsulation in classes."""

    def apply(self, filePath: str, data: AsFigoLintRule.VeribleSyntax.SyntaxData):
        for classNode in data.tree.iter_find_all({"tag": "kClassDeclaration"}):
            className = self.getClassName(classNode)

            numPublicVars = 0
            numProtectedVars = 0
            numLocalVars = 0

            for varNode in classNode.iter_find_all({"tag": "kDataDeclaration"}):
                qualifiers = self.getQualifiers(varNode)
                if "local" in qualifiers:
                    numLocalVars += 1
                elif "protected" in qualifiers:
                    numProtectedVars += 1
                else:
                    numPublicVars += 1  # Default to public

            numPrivateVars = numLocalVars + numProtectedVars
            if numPrivateVars < numPublicVars:
                message = (
                    f"Error: Poor encapsulation in class {className}\n"
                    f"Public vars: {numPublicVars}, Private vars: {numPrivateVars}"
                )
                self.linter.logViolation("R103",message)
