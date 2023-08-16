#!/usr/bin/env python3

import sys
import math

argv_list = [int(i) for i in sys.argv[1:]]

mean = sum(argv_list) / len(argv_list)
mean = int(mean) if mean.is_integer() else mean

print(f"""count={len(argv_list)}
unique={len(set(argv_list))}
minimum={min(argv_list)}
maximum={max(argv_list)}
mean={mean}
median={sorted(argv_list)[len(argv_list) // 2]}
mode={max(argv_list, key=argv_list.count)}
sum={sum(argv_list)}
product={math.prod(argv_list)}""")
