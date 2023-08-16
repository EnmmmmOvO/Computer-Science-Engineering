#!/usr/bin/python3 -u

import glob

for c_file in sorted(glob.glob("*.c")):
    print('gcc', '-c', c_file)
