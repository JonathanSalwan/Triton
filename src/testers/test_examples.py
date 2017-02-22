#!/usr/bin/env python2
# coding: utf-8
"""Tester for examples."""
import unittest
import subprocess
import os
import glob

EXAMPLE_DIR = os.path.join(os.path.dirname(__file__), "..", "examples", "python")


class TestExample(unittest.TestCase):

    """Holder to run examples as tests."""


for example in glob.iglob(os.path.join(EXAMPLE_DIR, "*.py")):
    if "small_x86-64_symbolic_emulator.py" in example:
        continue

    # Define an arguments with a default value as default value is capture at
    # lambda creation so that example_name is not in the closure of the lambda
    # function.
    setattr(TestExample, "test_" + os.path.basename(example),
            lambda self, example_name=example: subprocess.check_call(["python", example_name]))

