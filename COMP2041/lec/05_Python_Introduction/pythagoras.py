#! /usr/bin/env python3

"""
Compute Pythagoras' Theorem

written by d.brotherston@unsw.edu.au as a COMP(2041|9044) lecture example
translated from perl written by andrewt@cse.unsw.edu.au
"""

import math

x = float(input("Enter x: "))
y = float(input("Enter y: "))

pythagoras = math.sqrt(x**2 + y**2)

print(f"Square root of {x} squared + {y} squared is {pythagoras}")
