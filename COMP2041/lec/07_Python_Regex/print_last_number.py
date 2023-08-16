#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example

# Print the last number (real or integer) on every line
# Note: regexp to match number:  -?\d+\.?\d*
# Note: use of assignment operator :=

import re, sys

for line in sys.stdin:
    if m := re.search(r'(-?\d+\.?\d*)\D*$', line):
        print(m.group(1))
