#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example
# Python implementation of /bin/echo

import sys

if sys.argv[1:]:
    print(sys.argv[1], end='')
for arg in sys.argv[2:]:
    print('', arg, end='')
print()
