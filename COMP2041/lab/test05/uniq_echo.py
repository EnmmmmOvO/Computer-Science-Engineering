#!/usr/bin/env python3

import sys

list = []
for i in sys.argv[1:]:
    if i not in list:
        list.append(i)

print(' '.join(list))