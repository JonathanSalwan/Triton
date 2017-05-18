#!/usr/bin/env python2
# coding: utf-8
"""Tester for examples."""
import unittest
import subprocess
import os
import sys
import glob

EXAMPLE_DIR = os.path.join(os.path.dirname(__file__), "..", "..", "examples", "python")


class TestExample(unittest.TestCase):

    """Holder to run examples as tests."""


for example in glob.iglob(os.path.join(EXAMPLE_DIR, "*.py")):
    if "small_x86-64_symbolic_emulator.py" in example:
        continue

    def test_example(self, example_name=example):
        """Run example and show stdout in case of fail."""
        p = subprocess.Popen([sys.executable, example_name],
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE)
        out, err = p.communicate()
        self.assertEqual(p.returncode, 0, "\n".join((out, err, str(p.returncode))))

    # Define an arguments with a default value as default value is capture at
    # lambda creation so that example_name is not in the closure of the lambda
    # function.
    setattr(TestExample, "test_" + os.path.basename(example), test_example)
