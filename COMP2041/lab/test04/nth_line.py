#!/usr/bin/env python3

import sys

with open(sys.argv[2], 'r') as f:
    content = f.read().split('\n')[:-1]

try:
    print(content[int(sys.argv[1]) - 1])
except:
    exit()
    