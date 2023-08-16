#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Count the number of lines on standard input.

import sys

line_count = 0
for line in sys.stdin:
    line_count += 1
print(line_count, "lines")
