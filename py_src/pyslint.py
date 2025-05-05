# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
from pyslang import SyntaxTree
import argparse
import sys
import os
# Add the 'src' directory to the Python path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
import copy
import functools
from operator import countOf
import operator as op
import logging
from af_lint_rule import AsFigoLintRule
from asfigo_linter import AsFigoLinter
from rules.af_no_generic_mbx import NoGenericMBX

class PySLint(AsFigoLinter):
    def __init__(self, configFile="config.toml", logLevel=logging.INFO):
        super().__init__(configFile=configFile, logLevel=logLevel)
        self.prefix = "PySLint"
        # Automatically discover and register all subclasses of AsFigoLintRule
        self.rules = [rule_cls(self) for rule_cls in AsFigoLintRule.__subclasses__()]

    def loadSyntaxTree(self):
        tree = SyntaxTree.fromFile(self.testName)
        root = tree.root
        if str(root.members) == '':
            self.logViolation("AsFigo", f": No modules/interfaces/classes found in test file: {self.testName}")
            exit(0)
        return tree, root


    def runLinter(self):
        self.logInfo(self.prefix, f"Running PySLint for test file: {self.testName}")
        tree, root = self.loadSyntaxTree()
        for rule in self.rules:
            rule.run(tree)


        self.logSummary()


if __name__ == "__main__":
    pyslint = PySLint(configFile="config.toml", logLevel=logging.INFO)
    pyslint.runLinter()

