#! /usr/bin/env python3

"""
Simple example reading a line of input and examining characters
written by d.brotherston@unsw.edu.au as a COMP(2041|9044) lecture example
"""

try:
    line = input("Enter some input: ")
except EOFError:
    print("could not read any characters")
    exit(1)

n_chars = len(line)
print(f"That line contained {n_chars} characters")

if n_chars > 0:
    first_char = line[0]
    last_char = line[-1]
    print(f"The first character was '{first_char}'")
    print(f"The last character was '{last_char}'")
