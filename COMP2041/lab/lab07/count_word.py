#!/usr/bin/env python3

import sys, re

print(f'{sys.argv[1]} occurred {len([item for item in re.findall("[a-zA-Z]+", sys.stdin.read()) if item.lower() == sys.argv[1]])} times')