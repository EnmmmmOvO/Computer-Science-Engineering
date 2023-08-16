#!/usr/bin/env python3

import re, sys

result = list()

for i in sys.argv[1:]:
    if re.findall(r'[aeiou]{3}', i, re.IGNORECASE):
        result.append(i)

print(' '.join(result))