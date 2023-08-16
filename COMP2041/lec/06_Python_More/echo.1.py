#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example
# Python implementation of /bin/echo

# using indexing & range, not pythonesque

import sys

for i in range(1, len(sys.argv)):
    if i > 1:
        print(' ', end='')
    print(sys.argv[i], end='')
print()
