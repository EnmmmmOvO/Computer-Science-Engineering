#!/bin/dash

if [ $# -ne 1 ]; then
    echo "<Usage>: $0 backup_file"
    exit 1
fi

backup_file="$1"
i=0

if test ! -e "$backup_file"; then
    echo "${backup_file} not exists"
    exit 1
fi

while true; do
    if test ! -e ".${backup_file}.${i}"; then
        cp "${backup_file}" ".${backup_file}.${i}"
        echo "Backup of '${backup_file}' saved as '.${backup_file}.${i}'"
        break
    fi
    i=$((i + 1))
done