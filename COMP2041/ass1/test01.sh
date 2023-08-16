#!/bin/dash

# Test 01: Test Subset 0

PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT


{
  cd "$tmp1" || exit
  echo "$?"
  2041 pigs-init
  echo "$?"
  echo "Hello COMP2041" > "a"
  2041 pigs-add a
  echo "$?"
  2041 pigs-commit -m 'add a'
  echo "$?"
  2041 pigs-log
  echo "$?"
  2041 pigs-show :a
  echo "$?"
  2041 pigs-show 0:a
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  echo "$?"
  pigs-init
  echo "$?"
  echo "Hello COMP2041" > "a"
  pigs-add a
  echo "$?"
  pigs-commit -m 'add a'
  echo "$?"
  pigs-log
  echo "$?"
  pigs-show :a
  echo "$?"
  pigs-show 0:a
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test01_0(Add one file): Passed"
else
  echo "Test01_0(Add one file): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  echo "$?"
  2041 pigs-init
  echo "$?"
  echo "Hello COMP2041" > "a"
  2041 pigs-add a
  echo "$?"
  2041 pigs-commit -m 'add a 1'
  echo "$?"
  echo "Hi, hope have a high mark" > "a"
  2041 pigs-add a
  echo "$?"
  echo "Hi, hope have a high mark, yeah" > "a"
  2041 pigs-commit -m 'add a 2'
  echo "$?"
  2041 pigs-show :a
  echo "$?"
  2041 pigs-add a
  echo "$?"
  2041 pigs-commit -m 'add a 3'
  echo "$?"
  2041 pigs-show :a
  echo "$?"
  touch b c
  seq 9 > c
  2041 pigs-add b c
  echo "$?"
  2041 pigs-commit -m 'add b c'
  echo "$?"
  2041 pigs-log
  echo "$?"
  2041 pigs-show :c
  echo "$?"
  2041 pigs-show 1:a
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  echo "$?"
  pigs-init
  echo "$?"
  echo "Hello COMP2041" > "a"
  pigs-add a
  echo "$?"
  pigs-commit -m 'add a 1'
  echo "$?"
  echo "Hi, hope have a high mark" > "a"
  pigs-add a
  echo "$?"
  echo "Hi, hope have a high mark, yeah" > "a"
  pigs-commit -m 'add a 2'
  echo "$?"
  pigs-show :a
  echo "$?"
  pigs-add a
  echo "$?"
  pigs-commit -m 'add a 3'
  echo "$?"
  pigs-show :a
  echo "$?"
  touch b c
  seq 9 > c
  pigs-add b c
  echo "$?"
  pigs-commit -m 'add b c'
  echo "$?"
  pigs-log
  echo "$?"
  pigs-show :c
  echo "$?"
  pigs-show 1:a
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test01_1(Add Multiple file): Passed"
else
  echo "Test01_1(Add Multiple file): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "Hello COMP2041" > "a"
  2041 pigs-add a
  2041 pigs-commit -m 'add'
  2041 pigs-branch b1
  echo "Hello COMP2041" > "b"
  2041 pigs-add b
  2041 pigs-commit -m 'add'
  echo "Hello COMP2041" > "c"
  2041 pigs-add c
  2041 pigs-commit -m 'add'
  echo "Hello COMP2041" > "d"
  2041 pigs-add d
  2041 pigs-commit -m 'add'
  2041 pigs-checkout b1
  echo "Hello COMP2041" > "e"
  2041 pigs-add e
  2041 pigs-commit -m 'add'
  echo "Hello COMP2041, it is b1 branch" > "a"
  2041 pigs-add a
  2041 pigs-commit -m 'change a'
  2041 pigs-log
  echo "$?"
  2041 pigs-show :a
  echo "$?"
  2041 pigs-show master:a
  echo "$?"
  2041 pigs-checkout master
  2041 pigs-show :a
  echo "$?"
  2041 pigs-log
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "Hello COMP2041" > "a"
  pigs-add a
  pigs-commit -m 'add'
  pigs-branch b1
  echo "Hello COMP2041" > "b"
  pigs-add b
  pigs-commit -m 'add'
  echo "Hello COMP2041" > "c"
  pigs-add c
  pigs-commit -m 'add'
  echo "Hello COMP2041" > "d"
  pigs-add d
  pigs-commit -m 'add'
  pigs-checkout b1
  echo "Hello COMP2041" > "e"
  pigs-add e
  pigs-commit -m 'add'
  echo "Hello COMP2041, it is b1 branch" > "a"
  pigs-add a
  pigs-commit -m 'change a'
  pigs-log
  echo "$?"
  pigs-show :a
  echo "$?"
  pigs-show master:a
  echo "$?"
  pigs-checkout master
  pigs-show :a
  echo "$?"
  pigs-log
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test01_2(Multiple branch add, log and show): Passed"
else
  echo "Test01_2(Multiple branch add, log and show): failed"
fi