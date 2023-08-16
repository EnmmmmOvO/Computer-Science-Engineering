#!/bin/dash

# Detection || with &&

# a = 1
# b = 2
# c = 3
# test $a -ne '1' || test $b -eq '2' && test $c -ne '3' || echo "All tests passed"

tmp=$(mktemp)
tmp1=$(mktemp)
tmp2=$(mktemp)
trap 'rm "$tmp" "$tmp1" "$tmp2"' EXIT


echo "a=1\nb=2\nc=3\ntest \$a -ne '1' || test \$b -eq '2' && test \$c -ne '3' || echo \"All tests passed\"" > "$tmp"
dash "$tmp" > "$tmp1"
python3 "sheepy.py" "$tmp" | python3 > "$tmp2"

if ! diff "$tmp1" "$tmp2" > /dev/null 2>&1
then
    echo "test 2 Failed"
else
    echo "test 2 Passed"
fi
