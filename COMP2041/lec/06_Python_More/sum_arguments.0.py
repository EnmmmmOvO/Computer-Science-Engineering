#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# sum integers supplied as command line arguments
# no check that arguments are integers

import sys

total = 0
for arg in sys.argv[1:]:
    total += int(arg)
print("Sum of the numbers is", total)
