#!/bin/dash

for file in *; do 
    case $file in
    *.htm)
        if test -e "${file}l"; then
            echo "${file}l exists"
            exit 1
        else
            mv "${file}" "${file}l"
        fi
    esac

    
done