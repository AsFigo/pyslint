# ----------------------------------------------------
# SPDX-FileCopyrightText: Srinivasan Venkataramanan, 
#                         AsFigo Technologies, UK
# SPDX-License-Identifier: MIT
# ----------------------------------------------------

from pyslang import SyntaxTree
import argparse
import tomli
import os.path
import copy
import functools
from operator import countOf
import operator as op
import logging
import tomli


class BaseLintLogger:
    def __init__(self, prefix, configFile="config.toml", logLevel=logging.INFO):
        self.prefix = prefix
        self.logger = logging.getLogger(f"{prefix}Logger")
        self.logger.setLevel(logLevel)
        handler = logging.StreamHandler()
        handler.setLevel(logLevel)
        formatter = logging.Formatter('%(message)s')
        handler.setFormatter(formatter)
        if self.logger.hasHandlers():
            self.logger.handlers.clear()
        self.logger.addHandler(handler)
        self.rulesConfig = self.loadConfig(configFile)
        self.infoCount = 0
        self.warningCount = 0
        self.errorCount = 0

    def loadConfig(self, configFile):
        try:
            with open(configFile, "rb") as file:
                config = tomli.load(file)
            return config.get("rules", {})
        except FileNotFoundError:
            self.logger.warning(f"{self.prefix}: Config file '{configFile}' not found. Using default settings.")
            return {}

    def ruleEnabled(self, ruleId):
        return self.rulesConfig.get(ruleId, True)

    def logInfo(self, msg):
        self.infoCount += 1
        logMsg = f"{self.prefix}: INFO: {msg}"
        self.logger.info(logMsg)

    def logViolation(self, ruleId, msg, severity="WARNING"):
        if self.ruleEnabled(ruleId):
            logMsg = f"{self.prefix}: Violation: [{ruleId}]: {msg}"
            if severity == "ERROR":
                self.errorCount += 1
                self.logger.error(logMsg)
            elif severity == "WARNING":
                self.warningCount += 1
                self.logger.warning(logMsg)
            else:
                raise ValueError(f"Unsupported severity level: {severity}")
        else:
            self.logger.info(f"{self.prefix}: Rule [{ruleId}] is disabled and will not be logged.")

    def logSummary(self):
        self.logger.info(f"{self.prefix}: Summary: INFO: {self.infoCount}, WARNING: {self.warningCount}, ERROR: {self.errorCount}")


class AsFigoLinter(BaseLintLogger):
    def __init__(self, configFile="config.toml", logLevel=logging.INFO):
        super().__init__(prefix="AsFigo", configFile=configFile, logLevel=logLevel)
        self.args = self.parseArguments()
        self.testName = self.args.test

    def parseArguments(self):
        parser = argparse.ArgumentParser(description="AsFigoLinter Argument Parser")
        parser.add_argument("-t", "--test", required=True, help="Input test name (file path)")
        return parser.parse_args()

    def loadSyntaxTree(self):
        tree = SyntaxTree.fromFile(self.testName)
        root = tree.root
        if str(root.members) == '':
            print("AsFigo: No modules/interfaces/classes found")
            exit(0)
        return tree, root

    def runLinter(self):
        tree, root = self.loadSyntaxTree()
        self.logInfo(f"Loaded test file: {self.testName}")
        self.logViolation("R101", "Variable name does not follow naming conventions.")
        self.logViolation("R102", "Mandatory rule not followed; cannot proceed.", severity="ERROR")
        self.logSummary()


class PySlintLinter(AsFigoLinter):
    def __init__(self, configFile="config.toml", logLevel=logging.INFO):
        super().__init__(configFile=configFile, logLevel=logLevel)
        self.prefix = "PySlint"

    def runLinter(self):
        self.logInfo(f"Running PySlint for test file: {self.testName}")
        tree, root = self.loadSyntaxTree()
        self.logViolation("R101", "Variable name does not follow naming conventions.")
        self.logViolation("R102", "Mandatory rule not followed; cannot proceed.", severity="ERROR")
        self.logSummary()


if __name__ == "__main__":
    pyslint = PySlintLinter(configFile="config.toml", logLevel=logging.INFO)
    pyslint.runLinter()

