#!/usr/bin/env python3

import sys, re

with open(sys.argv[1], 'r') as f:
    content = f.read()

total = 0
for i in re.findall('[0-9]+', content):
    total += int(i)

print(total)