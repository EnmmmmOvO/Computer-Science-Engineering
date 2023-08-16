#!/usr/bin/env python3
import sys

reverse=str()
with open(sys.argv[1], 'r') as f:
    for i, line in enumerate(f, start=1):
        reverse = line + reverse

with open(sys.argv[2], 'w') as f:
    f.write(reverse)