#!/bin/dash

file="$1"

i=-1
sort -g "$file" | while read -r number; do
    if [ "$i" = -1 ]; then
        i="$number"
        i=$((i + 1))
    elif [ "$i" = "$number" ]; then
        i=$((i + 1))
    else
        while [ "$i" -lt "$number" ]; do
            echo "$i"
            i=$((i + 1))
        done
        i=$((i + 1))
    fi
done
