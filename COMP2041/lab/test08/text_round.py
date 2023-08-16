#!/usr/bin/env python3
import re


def round_numbers(match_obj):
    rounded = round(float(match_obj.group(0)))
    return str(rounded)


while True:
    try:
        print(re.sub(r'\d+\.?\d*', round_numbers, input()))
    except EOFError:
        break
