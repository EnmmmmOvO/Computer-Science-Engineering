#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Count the number of lines on standard input.

import sys

lines = sys.stdin.readlines()
line_count = len(lines)
print(line_count, "lines")
