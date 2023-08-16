#!/usr/bin/env python3

import sys

list = dict()
time = int(sys.argv[1])

while True:
    try:
        i = input()
        list[i] += 1
        if list[i] == time:
            print(f'Snap: {i}')
            break
    except KeyError:
        list[i] = 1
    except EOFError:
        break
