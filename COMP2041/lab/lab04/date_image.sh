#!/bin/dash

for pic in "$@"; do
    if test ! -e "$pic"; then
        echo "${pic} not exists"
        continue
    fi

    time=$(ls -l "${pic}" | sed -E -e 's/^.* ([A-Z][a-z]{2} [0-3][0-9] [0-2][0-9]:[0-5][0-9]) .*$/\1/')
    convert -gravity south -pointsize 36 -draw 'text 0,10 "'"$time"'"' "$pic" "temp_${pic}" && 
    mv "temp_${pic}" "$pic"

done