#!/usr/bin/env python3

import sys


for i in sys.stdin:
    line = list()
    for j in i.rstrip().split(' '):
        if not j: continue
        time = dict()
        for k in j:
            try:
                time[k.lower()] += 1
            except KeyError:
                time[k.lower()] = 1
        check = False
        record = -1
        for key, val in time.items():
            if record == -1:
                record = val
                continue
            elif record != val:
                check = True
                break
        if not check:
            line.append(j)

    print(' '.join(line))
