#!/usr/bin/env python3

import sys


record = dict()
for filename in sys.argv[1:]:
    with open(filename, 'r') as f:
        for line in f:
            content = line.split()
            fish = ' '.join(content[2:]).lower().rstrip('s')
            try:
                record[fish][0] += 1
                record[fish][1] += int(content[1])
            except KeyError:
                record[fish] = [1, int(content[1])]


for k, v in sorted(record.items()):
    print(f'{k} observations: {v[0]} pods, {v[1]} individuals')

