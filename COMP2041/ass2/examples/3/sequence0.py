#!/usr/bin/python3 -u

import subprocess
import sys

# print a contiguous integer sequence

start = sys.argv[1]
finish = sys.argv[2]

number = start
while int(number) <= int(finish):
    print(number)
    number = subprocess.run(['expr', number, '+', '1'], text=True, stdout=subprocess.PIPE).stdout.rstrip('\n') # increment number
