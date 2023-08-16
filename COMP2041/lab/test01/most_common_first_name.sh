#!/bin/dash 

sed -E -e 's/^.*, ([a-zA-Z]+) .*$/\1/' | sort | uniq -c | sort -n | tail -1 | sed -E 's/^[0-9 ]+//' 