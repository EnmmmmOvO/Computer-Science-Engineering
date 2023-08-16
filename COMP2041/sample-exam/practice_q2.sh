#!/bin/dash

grep -E '\|M$' | cut -d '|' -f 3 | sed -E -e 's/^([^,]+),.*$/\1/g' | sort | uniq