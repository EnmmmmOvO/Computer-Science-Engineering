#!/usr/bin/python3 -u
import os
import subprocess
import sys
start = 13
if len(sys.argv[1:]) > 0:
    start = sys.argv[1]
i = 0
number = start
file = './tmp.numbers'
subprocess.run(['rm', '-f', str(file)])
while not subprocess.run(['true']).returncode:
    if os.access(file, os.R_OK):
        if not subprocess.run(['fgrep', '-x', '-q', str(number), str(file)]).returncode:
            print('Terminating:', 'series', 'is', 'repeating')
            sys.exit(0)
    with open(file, 'a') as f:
        print(number, file=f)
    print(i, number)
    k = int(number) % 2
    if k == 1:
        number = 7 * int(number) + 3
    else:
        number = int(number) // 2
    i = i + 1
    if int(number) > 100000000 or int(number) < -100000000:
        print('Terminating:', 'too', 'large')
        sys.exit(0)
subprocess.run(['rm', '-f', str(file)])
