# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging

class NoGlobalVarsRule(AsFigoLintRule):
    """Detects global variables and raises violations."""

    def apply(self):
        message = f"Found global variable:  in file: "
        self.linter.logViolation("R104",message)  

