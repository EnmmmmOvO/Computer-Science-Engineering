#!/usr/bin/python3 -u

x = "###"
while x != "########":
    y = '#'
    while y != x:
        print(y)
        y = f"{y}#"
    x = f"{x}#"
