#!/bin/dash

# Detect the simultaneous presence of > or >> with <

# echo hi > file1.txt
# cat < file1.txt >> file.txt"
tmp=$(mktemp)
tmp1=$(mktemp)
tmp2=$(mktemp)
trap 'rm "$tmp" "$tmp1" "$tmp2"' EXIT

echo "echo hi > file1.txt\ncat < file1.txt >> file.txt" > "$tmp"
dash "$tmp" > "$tmp1"
python3 "sheepy.py" "$tmp" | python3 > "$tmp2"

if ! diff "$tmp1" "$tmp2" > /dev/null 2>&1
then
    echo "test 1 Failed"
else
    echo "test 1 Passed"
fi
