#!/usr/bin/env python3
import re

list = []
while True:
    try:
        list.append(input())
    except EOFError:
        break

for i in list:
    if re.match(r'^#', i):
        match = re.match(r'^#(\d+)', i)
        print(list[int(match.group(1)) - 1])
    else:
        print(i)