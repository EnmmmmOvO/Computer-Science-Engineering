#!/bin/dash

# Test 1
for name in Alice Bob Charlie; do
    echo "Hello, $name!"
done

fruit="apple"
while [ "$fruit" != "banana" ]
do # Test 2
    echo "The fruit is not a banana, it is a $fruit."
    fruit="banana"
done

if [ "$fruit" = "apple" ]
then # Test 3
    echo "It is an apple"
elif [ "$fruit" = "banana" ]; then
    echo "It is a banana"
else
    echo "Unknown fruit"
fi

# Test 4
echo 1 > file.txt # Test 5
test -e file.txt && echo "file.txt exists"
test -d file.txt || echo "file.txt is not dictionary"