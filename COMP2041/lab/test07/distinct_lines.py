#!/usr/bin/env python3


import sys


time = int(sys.argv[1])
input_sentence = list()
n = 0

try:
    while True:
        a = input().replace(' ', '').lower()
        n += 1
        if a not in input_sentence:
            input_sentence.append(a)
            if len(input_sentence) == time:
                print(f'{time} distinct lines seen after {n} lines read.')
                break


except EOFError:
    print(f'End of input reached after {n} lines read - {time} different lines not seen.')

