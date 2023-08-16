#! /usr/bin/env python3

"""
Create a string of size 2^n by concatenation
written by d.brotherston@unsw.edu.au as a COMP(2041|9044) lecture example
"""

import sys

if len(sys.argv) != 2:
    print(f"Usage: {sys.argv[0]}: <n>")
    exit(1)

n = 0
string = "@"

while n < int(sys.argv[1]):
    string *= 2
    # or `string += string`
    # or `string = string + string`
    n += 1

print(f"String of 2^{n} = {len(string)} characters created")
