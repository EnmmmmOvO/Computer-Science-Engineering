#!/usr/bin/env python3

import sys


with open(sys.argv[1], 'r') as f:
    line = f.read().split('\n')[:-1]

if not line:
    exit(0)

if len(line) % 2 == 0:
    print(f'{line[int(len(line) / 2) - 1]}\n{line[int(len(line) / 2)]}')
else:
    print(line[int(len(line) / 2)])
