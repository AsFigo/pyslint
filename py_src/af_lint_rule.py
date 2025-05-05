# ----------------------------------------------------
# SPDX-FileCopyrightText: AsFigo Technologies, UK
# SPDX-FileCopyrightText: VerifWorks, India
# SPDX-License-Identifier: MIT
# ----------------------------------------------------
import logging
from abc import ABC, abstractmethod

class AsFigoLintRule(ABC):
    """Base class for all linting rules."""

    rule_count = 0  # Class variable to track rules executed

    
    def __init__(self, linter):
        self.linter = linter  # Store the linter instance
        self.ruleID = 'SVALintDefaultRuleID'
        '''
        if not hasattr(self, "ruleID"):  # Ensure ruleID exists in subclasses
            raise ValueError(f"{self.__class__.__name__} must define a `ruleID` attribute!")
        '''


    @classmethod
    def get_rule_count(cls):
        return cls.rule_count  # Get the count of rules applied

    @abstractmethod
    def apply(self, tree):
        """Abstract method to apply the rule."""
        raise NotImplementedError


    def run(self, tree):
        """Wrapper method to automatically count and apply the rule."""
        AsFigoLintRule.rule_count += 1  # Automatically increment rule count
        message = (
                f"Running lint ruleID: {self.ruleID} on file: {self.linter.testName} \n"
                )

        self.linter.logInfo(self.ruleID, message)

        self.apply(tree)  # Call the actual rule logic
    '''
    def getClassName(self, classNode):
        """Extracts the class name from a class declaration."""
        for header in classNode.iter_find_all({"tag": "kClassHeader"}):
            for identifier in header.iter_find_all({"tag": "SymbolIdentifier"}):
                return identifier.text
        return "Unknown"

    def getQualifiers(self, varNode):
        """Extracts variable qualifiers (e.g., local, protected, rand)."""
        qualifiers = set()
        for qualList in varNode.iter_find_all({"tag": "kQualifierList"}):
            qualifiers.update(qualList.text.split())  # Extract words
        return qualifiers
    '''
