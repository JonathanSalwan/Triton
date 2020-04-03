#!/usr/bin/env python
# coding: utf-8
"""Tester for documentation."""
import unittest
import doctest
import os
import glob

SNIPPET_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "libtriton", "bindings", "python", "objects")

class TestDoc(unittest.TestCase):

    """Holder to run examples as tests."""


for i, example in enumerate(glob.iglob(os.path.join(SNIPPET_DIR, "*.cpp"))):

    # FIXME: Waiting for libboost1.71-all-dev in the Travis apt-package-safelist.
    if "pyAstContext.cpp" in example:
        continue

    def _test_snippet(self, example_name=example):
        """Run example and show stdout in case of fail."""
        res = doctest.testfile(example_name, module_relative=False)
        self.assertEqual(res.failed, 0)

    # Define an arguments with a default value as default value is capture at
    # lambda creation so that example_name is not in the closure of the lambda
    # function.
    setattr(TestDoc, "test_" + str(i) + "_" + os.path.basename(example), _test_snippet)
