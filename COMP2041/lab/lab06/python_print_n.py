#!/usr/bin/env python3

import sys

s = sys.argv[2]
for i in range(int(sys.argv[1])):
    s = f"print({repr(s)})"

print(s)