#!/bin/dash

PATH=$PATH:.

if [ $# -ne 1 ]; then
    echo "<Usage>: $0 snapshot_number"
    exit 1
fi

i=".snapshot.${1}"

if test ! -e "$i"; then
    echo "Snapshoe ${1} not exists"
    exit 1
fi

snapshot-save.sh

for file in *; do
    if [ "$file" != "snapshot-save.sh" ] && [ "$file" != "snapshot-load.sh" ]; then 
        rm "$file"
    fi
done

for file in "${i}/*"; do
    cp $file "./"
done

echo "Restoring snapshot ${1}"