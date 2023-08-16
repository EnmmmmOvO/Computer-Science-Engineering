#!/bin/dash 

cut -d'|' -f2,3 | sort | uniq | sed -E -e 's/^.*, ([a-zA-Z]+) .*$/\1/' | sort