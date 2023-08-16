#!/usr/bin/env python3
import sys


def caesar_shift(ch, n):
    if ch.isupper():
        return chr((ord(ch) - ord('A') + n) % 26 + ord('A'))
    elif ch.islower():
        return chr((ord(ch) - ord('a') + n) % 26 + ord('a'))
    else:
        return ch


number = int(sys.argv[1])
record = list()

for line in sys.stdin:
    record.append(''.join(caesar_shift(ch, number) for ch in line))

print(''.join(record), end='')
