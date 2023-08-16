#!/bin/dash

# Test 02: Mainly test all possible errors in subset 1

PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-init
  2041 pigs-commit -a -m 'test'
  echo "$?"
  2041 pigs-add a
  2041 pigs-commit -a -s test
  echo "$?"
  2041 pigs-log
  2041 pigs-commit -a -m test
  echo "$?"
  touch b c
  2041 pigs-commit -a -m test
  echo "$?"
  2041 pigs-log
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  pigs-commit -a -m 'test'
  echo "$?"
  pigs-add a
  pigs-commit -a -s test
  echo "$?"
  pigs-log
  pigs-commit -a -m test
  echo "$?"
  touch b c
  pigs-commit -a -m test
  echo "$?"
  pigs-log
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test02_0(pigs-show error): Passed"
else
  echo "Test02_0(pigs-show error): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-rm 
  echo "$?"
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -a -m 'test'
  2041 pigs-rm 
  echo "$?"
  2041 pigs-rm b
  echo "$?"
  2041 pigs-rm --cac
  echo "$?"
  2041 pigs-rm --force
  echo "$?"
  2041 pigs-rm --force -cached b
  echo "$?"
  2041 pigs-rm --cached --force b
  echo "$?"
  2041 pigs-rm --force --cached -a
  echo "$?"
  2041 pigs-rm a
  echo "$?"
  2041 pigs-rm --cached a
  echo "$?"
  2041 pigs-rm --force a
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-rm 
  echo "$?"
  pigs-init
  touch a
  pigs-add a
  pigs-commit -a -m 'test'
  pigs-rm 
  echo "$?"
  pigs-rm b
  echo "$?"
  pigs-rm --cac
  echo "$?"
  pigs-rm --force
  echo "$?"
  pigs-rm --force -cached b
  echo "$?"
  pigs-rm --cached --force b
  echo "$?"
  pigs-rm --force --cached -a
  echo "$?"
  pigs-rm a
  echo "$?"
  pigs-rm --cached a
  echo "$?"
  pigs-rm --force a
  echo "$?"
} > "$result2" 2>&1


if diff "$result1" "$result2" > /dev/null; then
  echo "Test02_1(pigs-rm error): Passed"
else
  echo "Test02_1(pigs-rm error): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-status
  echo "$?"
  2041 pigs-init
  2041 pigs-status
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-status
  echo "$?"
  pigs-init
  pigs-status
  echo "$?"
} > "$result2" 2>&1


if diff "$result1" "$result2" > /dev/null; then
  echo "Test02_2(pigs-status error): Passed"
else
  echo "Test02_2(pigs-status error): failed"
fi