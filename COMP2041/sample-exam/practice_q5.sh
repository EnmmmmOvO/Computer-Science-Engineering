#!/bin/dash

rg="$1"
file="$2"


year=$(grep -E "^$rg\|" "$file")

if [ -z "$year" ]; then
    echo "No award matching '${rg}'"
    exit 1 
fi

i=-1
echo "$year" | cut -d '|' -f 2 | sort | uniq | while read -r number; do
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



