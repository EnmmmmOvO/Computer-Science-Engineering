#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Simple cp implementation for text files using line-based I/O
# and with statement, but no error handling

import sys

if len(sys.argv) != 3:
    print("Usage:", sys.argv[0], "<infile> <outfile>", file=sys.stderr)
    sys.exit(1)

with open(sys.argv[1]) as infile:
    with open(sys.argv[2], "w") as outfile:
        for line in infile:
            outfile.write(line)
