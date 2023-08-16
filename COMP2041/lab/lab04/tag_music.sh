#!/bin/dash

for dic do
    dic=$(echo "$dic" | sed 's/\/$//g')
    year=$(echo "$dic" | sed -E -e 's/^.*\/.* ([0-9]{4})$/\1/') 
    album=$(echo "$dic" | sed -E -e 's/^.*\/([^\/]+)$/\1/')
    for music in "$dic"/*; do
        title=$(echo "$music" | sed -E -e 's/^.*- (.+) -.*$/\1/')
        track=$(echo "$music" | sed -E -e 's/^.*\/([0-9]+) - .+ -.*$/\1/')
        artist=$(echo "$music" | sed -E -e 's/^.*- .+ - (.+)\.mp3$/\1/')
        id3 -t "$title" -T "$track" -a "$artist" -A "$album" -y "$year" "$music" >/dev/null
    done
done