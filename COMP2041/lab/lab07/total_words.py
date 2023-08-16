#!/usr/bin/env python3

import re, sys


print(f'{len(re.findall("[a-zA-Z]+", sys.stdin.read()))} words')