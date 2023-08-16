#!/bin/dash

small=""
medium=""
large=""

for i in *
do 
    size=$(cat "$i" | wc -l)
    if [ $size -lt 10 ]; then
        small="${small} $i"
    elif [ $size -ge 100 ]; then
        large="${large} $i"
    else
        medium="${medium} $i"
    fi
done

echo "Small files:${small}"
echo "Medium-sized files:${medium}"
echo "Large files:${large}"