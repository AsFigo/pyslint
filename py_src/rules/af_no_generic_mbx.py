# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from af_lint_rule import AsFigoLintRule
import logging

class NoGenericMBX(AsFigoLintRule):
    """Detects generic Mailbox declaration"""

    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = "NoGenericMBX"

    def apply(self, tree):
        self.ruleID = 'NoGenericMBX'

        for scope_i in (tree.root.members):
            if (scope_i.kind.name == 'ClassDeclaration'):
                for cl_item in (scope_i.items):

                    if (cl_item.kind.name != 'ClassPropertyDeclaration'):
                        continue
                    lv_code_s = str(cl_item)
                    lv_cl_prop_s = str(cl_item.declaration.type)
                    if (cl_item.declaration.type.kind.name != 'NamedType'):
                        continue
                    message = (
                            "A generic mailbox declaration was found. "
                            "While IEEE 1800 LRM allows this, such usage is error-prone and harder to debug. "
                            "Verilator does not support this feature. Please use typed mailbox such as:"
                            "'mailbox #(int) in_box;' \n"
                            f"Source code snippet: \n{lv_code_s}"
                            )

                    if ( ('mailbox' in lv_cl_prop_s) and
                        ('#' not in lv_cl_prop_s)):
                        self.linter.logViolation(self.ruleID,message)  

