#!/usr/bin/env python3

import sys

total = 0

for i in sys.argv[1:]:
    with open(i, 'r') as f:
        content = f.read()
    for i in content.split(' Orca'):
        try:
            total += int(i.split(' ')[-1])
        except ValueError:
            break

print(f'{total} Orcas reported')
