#!/usr/bin/env python3

import glob, re, sys

result = dict()
word = sys.argv[1]

for i in glob.glob('lyrics/*.txt'):
    with open(i, 'r') as f:
        word_list = re.findall("[a-zA-Z]+", f.read())
    result[i.replace('lyrics/', '').replace('.txt', '').replace('_', ' ')] = [len(word_list),
                                                            len([item for item in word_list if item.lower() == word])]

for i, j in sorted(result.items()):
    print(f"{j[1]:4}/{j[0]:6} = {j[1] / j[0]:.9f} {i}")