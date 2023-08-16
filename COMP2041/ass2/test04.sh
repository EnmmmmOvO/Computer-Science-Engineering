#!/bin/dash

# Testing comment.

# echo not comment # Testing comment.

tmp=$(mktemp)
tmp1=$(mktemp)
tmp2=$(mktemp)
trap 'rm "$tmp" "$tmp1" "$tmp2"' EXIT

echo "echo not comment # Testing comment" > "$tmp"

dash "$tmp" > "$tmp1"
python3 "sheepy.py" "$tmp" | python3 > "$tmp2"

if ! diff "$tmp1" "$tmp2" > /dev/null 2>&1
then
    echo "test 4 Failed"
else
    echo "test 4 Passed"
fi