#!/bin/dash

i=0
while true; do
    if test ! -e ".snapshot.${i}"; then
        mkdir ".snapshot.${i}"
        break
    fi
    i=$((i + 1))
done

echo "Creating snapshot ${i}"
dic=".snapshot.${i}"

for file in *; do
    if [ "$file" != "snapshot-save.sh" ] && [ "$file" != "snapshot-load.sh" ]; then 
        cp "$file" "${dic}/${file}"
    fi
done