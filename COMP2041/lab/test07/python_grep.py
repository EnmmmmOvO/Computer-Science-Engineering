#!/usr/bin/env python3

import re
import sys

pattern = re.compile(sys.argv[1])

with open(sys.argv[2]) as f:
    for line in f:
        if pattern.search(line):
            print(line, end='')