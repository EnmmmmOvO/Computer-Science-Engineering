#!/usr/bin/env python3


import sys


with open(sys.argv[1], 'r') as f:
    file1 = f.read().split('\n')[:-1]

with open(sys.argv[2], 'r') as f:
    file2 = f.read().split('\n')[:-1]

if len(file1) != len(file2):
    print(f'Not mirrored: different number of lines: {len(file1)} versus {len(file2)}')
    sys.exit()

for idx, line in enumerate(file1):
    if line not in file2:
        print(f'Not mirrored: line {idx + 1} different')
        sys.exit()
    
print('Mirrored')