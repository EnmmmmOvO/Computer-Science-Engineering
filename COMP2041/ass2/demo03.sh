#!/bin/dash

# Test 1
string1="Hello"
string2="World"
echo "$string1 $string2!"

string3="Dash" # Test 2
string4="Scripting"
combined="${string3}${string4}"
echo $combined # Test 3
echo "$string3 $string4"
echo '$string3 $string4' # Test 4
echo $string3 $string4

for word in COMP9417 COMP3151 COMP2041 # Test 5
do
    echo "Word is: $word"
done

# Test 6
name="William"
echo $name > file.txt
length=$(wc file.txt)
echo "Length of the string $name is: $length" # Test 7
