#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example
# Python implementation of /bin/echo

# using indexing & while, not pythonesque

import sys

i = 1
while i < len(sys.argv):
    if i > 1:
        print(" ", end="")
    print(sys.argv[i], end="")
    i += 1
print()
