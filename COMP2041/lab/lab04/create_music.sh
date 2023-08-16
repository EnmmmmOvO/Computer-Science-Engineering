#!/bin/dash

copy_file="$1"
source_dict="$2"

year=1992
time=10
path=""
mkdir "$source_dict"

wget -q -O- 'https://en.wikipedia.org/w/index.php?title=Triple_J_Hottest_100&oldid=1156459050&action=raw' | grep -A 11 -E "Triple J Hottest 100, [0-9]{4}\|[0-9]{4}" | grep -E '^#.* – .*$' | sed -E 's/\[\[[^\[\|]+\|//g' | sed -E 's/[]"[]//g' | sed -E 's/^# ?//g' | sed 's/\//-/g' | while read -r line; do
    time=$((time + 1))
    if [ "$time" -eq 11 ]
    then
        time=1
        year=$((year + 1))
        path="${source_dict}/Triple J Hottest 100, ${year}"
        mkdir "$path"
    fi
    part_1=$(echo "$line" | sed -E -e 's/^(.*) – .*$/\1/')
    part_2=$(echo "$line" | sed -E -e 's/^.* – (.*)$/\1/')
    cp "$copy_file" "${path}/${time} - ${part_2} - ${part_1}.mp3"
done