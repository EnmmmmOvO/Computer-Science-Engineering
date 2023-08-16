#!/bin/dash

check=0
list=''
for i in "$@"; do
    list="$list $i"
    for j in "$@"; do
        if echo "$list" | grep -E "$j" > /dev/null; then
            continue
        fi
        
        diff "$i" "$j" > /dev/null || continue

        echo "ln -s ${i} ${j}"
        list="$list $j"
        check=1
    done
done

test "$check" = 0 && echo "No files can be replaced by symbolic links"