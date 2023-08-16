#!/bin/dash

echo "Hello, World!"
echo "Demonstrating echo with variables" # Test 1

x=10
echo "The value of x is $x"
# Test 2
y=20
echo "The value of y is $y"

name="William"
echo "Welcome, ${name}"

result=$(echo "COMP2041 is great!")
echo $result

echo hello world > 1.txt
echo -n My name is william >> 1.txt

for var in 1 2 3 4 5; do # Test 3
    echo "Var value: $var"
done
