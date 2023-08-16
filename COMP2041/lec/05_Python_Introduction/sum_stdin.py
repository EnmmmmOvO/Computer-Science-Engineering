#! /usr/bin/env python3

"""
Read numbers until end of input (or a non-number) is reached
Then print the sum of the numbers

written by d.brotherston@unsw.edu.au as a COMP(2041|9044) lecture example
translated from perl written by andrewt@cse.unsw.edu.au
"""

from sys import stdin

sum = 0

for line in stdin:

    line = line.strip()

    try:
        sum += int(line)
    except ValueError as e:
        print(e)

print(f"Sum of the numbers is {sum}")
