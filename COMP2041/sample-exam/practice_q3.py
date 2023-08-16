#!/usr/bin/env python3

import sys
import re


result = set()
for i in sys.stdin:
    if re.search(r'\|M$', i):
        result.add(i.split('|')[2].split(',')[0])

print('\n'.join(sorted(result)))