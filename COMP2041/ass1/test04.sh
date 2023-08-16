#!/bin/dash

# Test 04: Test pigs-rm [-force] [-cached] <filename>

PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  2041 pigs-rm a
  2041 pigs-status
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b
  pigs-add a
  pigs-commit -m 'first commit'
  pigs-rm a
  pigs-status
  ls -1
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test04_0(pigs-rm normal): Passed"
else
  echo "Test04_0(pigs-rm normal): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  echo a > a
  2041 pigs-rm -cached a
  echo "$?"
  2041 pigs-status
  ls -1
  2041 pigs-add a
  2041 pigs-rm -cached a
  echo "$?"
  2041 pigs-status
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b
  pigs-add a
  pigs-commit -m 'first commit'
  echo a > a
  pigs-rm -cached a
  echo "$?"
  pigs-status
  ls -1
  pigs-add a
  pigs-rm -cached a
  echo "$?"
  pigs-status
  ls -1
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test04_1(pigs-rm cached): Passed"
else
  echo "Test04_1(pigs-rm cached): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  echo a > a
  2041 pigs-rm -force a
  echo "$?"
  2041 pigs-status
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b
  pigs-add a
  pigs-commit -m 'first commit'
  echo a > a
  pigs-rm -force a
  echo "$?"
  pigs-status
  ls -1
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test04_2(pigs-rm force): Passed"
else
  echo "Test04_2(pigs-rm force): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  echo a > a
  2041 pigs-rm -cached a
  echo "$?"
  2041 pigs-status
  ls -1
  2041 pigs-rm -force -cached a
  echo "$?"
  2041 pigs-status
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b
  pigs-add a
  pigs-commit -m 'first commit'
  echo a > a
  pigs-rm -cached a
  echo "$?"
  pigs-status
  ls -1
  pigs-rm -force -cached a
  echo "$?"
  pigs-status
  ls -1
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test04_3(pigs-rm force cached): Passed"
else
  echo "Test04_3(pigs-rm force cached): failed"
fi

rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b c d e
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  2041 pigs-status
  2041 pigs-rm a
  echo "$?"
  2041 pigs-status
  ls -1
  2041 pigs-add b
  2041 pigs-commit -m 'second commit'
  2041 pigs-rm --cached a
  echo "$?"
  2041 pigs-status
  ls -1
  2041 pigs-add c
  2041 pigs-commit -m 'third commit'
  echo 1 > c
  2041 pigs-rm a
  echo "$?"
  2041 pigs-rm --cached a
  echo "$?"
  2041 pigs-rm --force a
  echo "$?"
  2041 pigs-status
  ls -1
  2041 pigs-add d
  2041 pigs-commit -m 'third commit'
  echo 2 > d
  2041 pigs-add d
  2041 pigs-rm a
  echo "$?"
  2041 pigs-rm --cached a
  echo "$?"
  2041 pigs-status
  ls -1
  
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b c d e
  pigs-add a
  pigs-commit -m 'first commit'
  pigs-status
  pigs-rm a
  echo "$?"
  pigs-status
  ls -1
  pigs-add b
  pigs-commit -m 'second commit'
  pigs-rm --cached a
  echo "$?"
  pigs-status
  ls -1
  pigs-add c
  pigs-commit -m 'third commit'
  echo 1 > c
  pigs-rm a
  echo "$?"
  pigs-rm --cached a
  echo "$?"
  pigs-rm --force a
  echo "$?"
  pigs-status
  ls -1
  pigs-add d
  pigs-commit -m 'third commit'
  echo 2 > d
  pigs-add d
  pigs-rm a
  echo "$?"
  pigs-rm --cached a
  echo "$?"
  pigs-status
  ls -1
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test04_4(pigs-rm multiple file): Passed"
else
  echo "Test04_4(pigs-rm multiple file): failed"
fi
