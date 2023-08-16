#!/bin/dash 

cut -d'|' -f2 | sort | uniq -c | sed -n 's/^ *2 //p' | sort -n
