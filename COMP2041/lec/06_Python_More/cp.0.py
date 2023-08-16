#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Simple cp implementation for text files using line-based I/O
# explicit close is used below, a with statement would be better
# no error handling

import sys

if len(sys.argv) != 3:
    print("Usage:", sys.argv[0], "<infile> <outfile>", file=sys.stderr)
    sys.exit(1)

infile = open(sys.argv[1], "r", encoding="utf-8")
outfile = open(sys.argv[2], "w", encoding="utf-8")
for line in infile:
    print(line, end='', file=outfile)
infile.close()
outfile.close()
