#!/bin/dash

# Test 00: Mainly test all possible errors in subset 0

PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-init a
  echo "$?"
  2041 pigs-init
  echo "$?"
  2041 pigs-init
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init a
  echo "$?"
  pigs-init
  echo "$?"
  pigs-init
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test00_0(pigs-init error): Passed"
else
  echo "Test00_0(pigs-init error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-add
  echo "$?"
  2041 pigs-init
  echo "$?"
  2041 pigs-add
  echo "$?"
  2041 pigs-add b
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-add
  echo "$?"
  pigs-init
  echo "$?"
  pigs-add
  echo "$?"
  pigs-add b
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test00_1(pigs-add error): Passed"
else
  echo "Test00_1(pigs-add error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)


{
  cd "$tmp1" || exit
  2041 pigs-commit
  echo "$?"
  2041 pigs-commit -m
  echo "$?"
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m
  echo "$?"
  2041 pigs-commit -s test
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-commit
  echo "$?"
  pigs-commit -m
  echo "$?"
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m
  echo "$?"
  pigs-commit -s test
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test00_2(pigs-commit error): Passed"
else
  echo "Test00_2(pigs-commit output): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-log
  echo "$?"
  2041 pigs-init
  2041 pigs-log
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-log
  echo "$?"
  pigs-init
  pigs-log
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test00_3(pigs-log error): Passed"
else
  echo "Test00_3(pigs-log output): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-show
  echo "$?"
  2041 pigs-init
  2041 pigs-show
  echo "$?"
  touch a
  2041 pigs-add a
  2041 pigs-commit -m 'test'
  2041 pigs-show test
  echo "$?"
  2041 pigs-show :b
  echo "$?"
  2041 pigs-show master:b
  echo "$?"
  2041 pigs-show v1:a
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-show
  echo "$?"
  pigs-init
  pigs-show
  echo "$?"
  touch a
  pigs-add a
  pigs-commit -m 'test'
  pigs-show test
  echo "$?"
  pigs-show :b
  echo "$?"
  pigs-show master:b
  echo "$?"
  pigs-show v1:a
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test00_4(pigs-show error): Passed"
else
  echo "Test00_4(pigs-show output): failed"
fi
