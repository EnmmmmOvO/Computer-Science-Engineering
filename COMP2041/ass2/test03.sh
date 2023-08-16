#!/bin/dash

# Testing multiple conditions in if statements and while loops.

# a=1
# if test $a -eq 1 && [ $a = 1 ] || [ $a != 1 ]
# then
#     echo "1 == 1"
# fi
# while test $a -eq 1 && [ $a = 1 ] || [ $a != 2 ]
# do
#     echo "1 == 1"
#     a=2
# done

tmp=$(mktemp)
tmp1=$(mktemp)
tmp2=$(mktemp)
trap 'rm "$tmp" "$tmp1" "$tmp2"' EXIT

echo "a=1\nif test \$a -eq 1 && [ \$a = 1 ] || [ \$a != 1 ]\nthen\n    echo \"1 == 1\"\nfi" > "$tmp"
echo "while test \$a -eq 1 && [ \$a = 1 ] || [ \$a != 2 ]\ndo\n    echo \"1 == 1\"\n    a=2\ndone" >> "$tmp"

dash "$tmp" > "$tmp1"
python3 "sheepy.py" "$tmp" | python3 > "$tmp2"

if ! diff "$tmp1" "$tmp2" > /dev/null 2>&1
then
    echo "test 3 Failed"
else
    echo "test 3 Passed"
fi