#!/bin/dash

# Test 03: Test pigs-commit [-a] -m and pigs-status

PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  echo "$?"
  touch b c
  2041 pigs-commit -a -m 'first commit'
  echo "$?"
  2041 pigs-status
  echo "Hello" > a
  2041 pigs-add b
  2041 pigs-commit -a -m 'first commit'
  echo "$?"
  2041 pigs-status 
  2041 pigs-show :a
  rm a
  2041 pigs-commit -a -m 'delete a'
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m 'first commit'
  echo "$?"
  touch b c
  pigs-commit -a -m 'first commit'
  echo "$?"
  pigs-status
  echo "Hello" > a
  pigs-add b
  pigs-commit -a -m 'first commit'
  echo "$?"
  pigs-status 
  pigs-show :a
  rm a
  pigs-commit -a -m 'delete a'
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test03_0(pigs-commit -a option test): Passed"
else
  echo "Test03_0(pigs-commit -a option test): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a b c d e f g h pigs-add pigs-branch
  2041 pigs-add a b c d e f
  2041 pigs-commit -m 'first commit'
  echo hello > a
  echo hello world > b
  2041 pigs-commit -a -m 'second commit'
  echo 2041 >> a
  echo shell >> b
  echo hello world > c
  2041 pigs-add a
  echo python >> b
  rm d
  2041 pigs-rm e
  2041 pigs-add g
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a b c d e f g h pigs-add pigs-branch
  pigs-add a b c d e f
  pigs-commit -m 'first commit'
  echo hello > a
  echo hello world > b
  pigs-commit -a -m 'second commit'
  echo >> a
  echo shell >> b
  echo hello world > c
  pigs-add a
  echo python >> b
  rm d
  pigs-rm e
  pigs-add g
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test03_1(pigs-status all situation test): Passed"
else
  echo "Test03_1(pigs-status all situation test): failed"
fi
rm -rf "$tmp1" "$tmp2" 
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  2041 pigs-status
  touch a 
  2041 pigs-add a
  2041 pigs-commit -m 'first commit'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  echo bbb > b
  2041 pigs-add b
  2041 pigs-commit -a -m 'second commit'
  2041 pigs-status
  2041 pigs-checkout master
  touch c
  2041 pigs-add c
  2041 pigs-commit -m 'third commit'
  2041 rm --cached a
  2041 pigs-status

} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  pigs-status
  touch a 
  pigs-add a
  pigs-commit -m 'first commit'
  pigs-branch b1
  pigs-checkout b1
  echo bbb > b
  pigs-add b
  pigs-commit -a -m 'second commit'
  pigs-status
  pigs-checkout master
  touch c
  pigs-add c
  pigs-commit -m 'third commit'
  rm --cached a
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test03_2(pigs-status with different branch): Passed"
else
  echo "Test03_2(pigs-status with different branch): failed"
fi