#!/usr/bin/env python3

import sys
import re

max = int(sys.argv[1])
with open(sys.argv[2], 'r') as f:
    content = f.read().split('\n')[:-1]

output = str()
for i in content:
    start = 0
    length = len(i)
    while start + max < length - 1:
        if i[start + max - 1] == ' ':
            output += i[start:start + max] + '\n'
            start += max
        elif ' ' not in i[start:start + max]:
            line = re.match(r'([^ ]+) ?', i[start:]).group(1)
            start += len(line) + 1
            output += line + '\n'
        else:
            line = re.match(r'(.* +)[^ ]+', i[start:start + max]).group(1)
            start += len(line)
            output += line + '\n'
    output += i[start:] + '\n'

with open(sys.argv[2], 'w') as f:
    f.write(output)