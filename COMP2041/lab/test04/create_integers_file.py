#!/usr/bin/env python3

import sys

content=str()
for i in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    content = content + str(i) + '\n'

with open(sys.argv[3], 'w') as f:
    f.write(content)