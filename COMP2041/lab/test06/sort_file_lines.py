#!/usr/bin/env python3

import sys

with open(sys.argv[1], 'r') as f:
    line = f.read().split('\n')[:-1]

print('\n'.join(sorted(line, key=lambda s: (len(s), s))))
