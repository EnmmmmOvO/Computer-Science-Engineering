#!/bin/dash

# Nested command substitutions.

# echo "Today date is: $(echo $(date +%Y-%m-%d))"

tmp=$(mktemp)
tmp1=$(mktemp)
tmp2=$(mktemp)
trap 'rm "$tmp" "$tmp1" "$tmp2"' EXIT

echo "echo \"Today date is: \$(echo \$(date +%Y-%m-%d))\"" > "$tmp"
dash "$tmp" > "$tmp1"
python3 "sheepy.py" "$tmp" | python3 > "$tmp2"

if ! diff "$tmp1" "$tmp2" > /dev/null 2>&1
then
    echo "test 0 Failed"
else
    echo "test 0 Passed"
fi
