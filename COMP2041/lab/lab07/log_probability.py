#!/usr/bin/env python3

import re, glob, sys, math

result = dict()
search_word = sys.argv[1:]

for i in glob.glob('lyrics/*.txt'):
    with open(i, 'r') as f:
        word_list = re.findall("[a-zA-Z]+", f.read())
    total = 0.0
    for word in search_word:
        total += math.log((len([item for item in word_list if item.lower() == word]) + 1) / len(word_list))
    result[i.replace('lyrics/', '').replace('.txt', '').replace('_', ' ')] = total

for i, j in sorted(result.items()):
    print(f"{j:10.5f} {i}")