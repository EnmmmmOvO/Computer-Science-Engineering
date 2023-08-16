#! /usr/bin/env python3


import os
import re
import sys
import collections

a = collections.deque()

def situation(action):
    if not action:
        return ''
    if re.search(r'^#!', action):
        return
    elif re.search(r'^#', action):
        return action
    elif re.search(r'=', action):
        var =



def main():
    output = ['#!/usr/bin/env python3']
    for i in sys.stdin.read().split('\n')[:-1]:
        situation(i.replace(' ', ''))
    print('\n'.join(output))


if __name__ == "__main__":
    main()
