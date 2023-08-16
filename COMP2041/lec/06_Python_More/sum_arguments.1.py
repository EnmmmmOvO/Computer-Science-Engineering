#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# sum integers supplied as command line arguments

import sys

total = 0
for arg in sys.argv[1:]:
    try:
        total += int(arg)
    except ValueError:
        print(f"error: '{arg}' is not an integer", file=sys.stderr)
        sys.exit(1)
print("Sum of the numbers is", total)
