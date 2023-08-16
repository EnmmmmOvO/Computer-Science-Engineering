#!/bin/dash


for jpg_file in *.jpg; do
    png_file=$(echo "$jpg_file" | sed 's/jpg$/png/g')
    
    if test -e "$png_file"
    then
        echo "${png_file} already exists"
    else
        convert "$jpg_file" "$png_file"
    fi
done