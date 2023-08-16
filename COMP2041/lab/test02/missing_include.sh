#!/bin/dash


for file in "$@"; do
    sed -E -n 's/#include "(.*)"/\1/p' "$file" | sort | while read -r h_file; do
        if test ! -e "$h_file"
        then
            echo "${h_file} included into ${file} does not exist"
        fi
    done
done