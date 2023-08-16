#!/usr/bin/env python3

import re, glob, sys, math


word_list = dict()
for i in glob.glob('lyrics/*.txt'):
    with open(i, 'r') as f:
        word_list[i.replace('lyrics/', '').replace('.txt', '').replace('_', ' ')] = re.findall('[a-zA-Z]+', f.read())


for song in sys.argv[1:]:
    with open(song, 'r') as f:
        search_word = re.findall('[a-zA-Z]+', f.read())

    max_probability = []
    for i, j in word_list.items():
        total = 0
        for k in search_word:
            total += math.log((len([item for item in j if item.lower() == k.lower()]) + 1) / len(j))
        if not max_probability or total > max_probability[1]:
            max_probability = [i, total]
    print(f'{song} most resembles the work of {max_probability[0]} (log-probability={max_probability[1]:.1f})')