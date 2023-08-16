#!/usr/bin/env python3

import re, sys

lines = []
max_number = float('-inf')

for line in sys.stdin:
    numbers = [float(n) for n in re.findall(r'[+-]?\d+\.?\d*', line)]

    if not numbers:
        continue

    line_max = max(numbers)
    if line_max > max_number:
        max_number = line_max
        lines = [line]
    elif line_max == max_number:
        lines.append(line)

for line in lines:
        print(line, end='')
