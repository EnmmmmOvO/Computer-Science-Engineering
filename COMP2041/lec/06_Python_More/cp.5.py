#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Simple cp implementation by running /bin/cp

import subprocess
import sys

if len(sys.argv) != 3:
    print("Usage:", sys.argv[0], "<infile> <outfile>", file=sys.stderr)
    sys.exit(1)

p = subprocess.run(['cp', sys.argv[1], sys.argv[2]])
sys.exit(p.returncode)