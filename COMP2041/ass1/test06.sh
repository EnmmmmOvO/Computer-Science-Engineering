#!/bin/dash


PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-checkout
  echo "$?"
  2041 pigs-init
  2041 pigs-checkout
  echo "$?"
  touch a
  2041 pigs-add a
  2041 pigs-commit -m test
  2041 pigs-checkout
  echo "$?"
  2041 pigs-checkout b1
  echo "$?"
  2041 pigs-branch b1
  echo "hello" > b
  2041 pigs-add b
  2041 pigs-commit -m "add b"
  2041 pigs-checkout b1
  echo "$?"
  echo "2041" > b
  2041 pigs-add b
  2041 pigs-commit -m "add b"
  echo "shell" > b
  2041 pigs-checkout master
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-checkout
  echo "$?"
  pigs-init
  pigs-checkout
  echo "$?"
  touch a
  pigs-add a
  pigs-commit -m test
  pigs-checkout
  echo "$?"
  pigs-checkout b1
  echo "$?"
  pigs-branch b1
  echo "hello" > b
  pigs-add b
  pigs-commit -m "add b"
  pigs-checkout b1
  echo "$?"
  echo "2041" > b
  pigs-add b
  pigs-commit -m "add b"
  echo "shell" > b
  pigs-checkout master
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test06_0(pigs-checkout error): Passed"
else
  echo "Test06_0(pigs-checkout error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "this is master" > a
  echo "this is master" > b
  echo "this is master" > c
  echo "this is master" > d
  2041 pigs-add a b c d
  2041 pigs-commit -m 'master add'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1" > b
  echo "this is b1" > c
  echo "this is b1" > d
  2041 pigs-commit -a -m 'master add'
  touch a b c d
  2041 pigs-checkout master
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "this is master" > a
  echo "this is master" > b
  echo "this is master" > c
  echo "this is master" > d
  pigs-add a b c d
  pigs-commit -m 'master add'
  pigs-branch b1
  pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1" > b
  echo "this is b1" > c
  echo "this is b1" > d
  pigs-commit -a -m 'master add'
  touch a b c d
  pigs-checkout master
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test06_1(pigs-checkout more than one file changed error): Passed"
else
  echo "Test06_1(pigs-checkout more than one file changed error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "this is master" > a
  2041 pigs-add a
  2041 pigs-commit -m 'master add'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  2041 pigs-commit -a -m 'master add'
  2041 pigs-checkout master
  ls -1
  2041 pigs-status
  cat a
  2041 pigs-show b1:a
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "this is master" > a
  pigs-add a
  pigs-commit -m 'master add'
  pigs-branch b1
  pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  pigs-commit -a -m 'master add'
  pigs-checkout master
  ls -1
  pigs-status
  cat a
  pigs-show b1:a
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test06_2(pigs-checkout test): Passed"
else
  echo "Test06_2(pigs-checkout test): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "this is master" > a
  2041 pigs-add a
  2041 pigs-commit -m 'master add'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1 b" > b
  2041 pigs-commit -a -m 'master add'
  2041 pigs-checkout master
  ls -1
  2041 pigs-status
  cat a
  cat b
  2041 pigs-add b
  2041 pigs-commit -a -m 'master add 2'
  2041 pigs-status
  2041 pigs-checkout b1 
  ls -1
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "this is master" > a
  pigs-add a
  pigs-commit -m 'master add'
  pigs-branch b1
  pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1 b" > b
  pigs-commit -a -m 'master add'
  pigs-checkout master
  ls -1
  pigs-status
  cat a
  cat b
  pigs-add b
  pigs-commit -a -m 'master add 2'
  pigs-status
  pigs-checkout b1 
  ls -1
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test06_3(pigs-checkout change but not add file): Passed"
else
  echo "Test06_3(pigs-checkout change but not add file): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "this is master" > a
  2041 pigs-add a
  2041 pigs-commit -m 'master add'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1 b" > b
  2041 pigs-commit -a -m 'master add'
  2041 pigs-add b
  2041 pigs-checkout master
  ls -1
  2041 pigs-status
  cat a
  cat b
  2041 pigs-commit -a -m 'master add 2'
  2041 pigs-status
  2041 pigs-checkout b1 
  ls -1
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "this is master" > a
  pigs-add a
  pigs-commit -m 'master add'
  pigs-branch b1
  pigs-checkout b1
  ls -1
  cat a
  echo "this is b1" > a
  echo "this is b1 b" > b
  pigs-commit -a -m 'master add'
  pigs-add b
  pigs-checkout master
  ls -1
  pigs-status
  cat a
  cat b
  pigs-commit -a -m 'master add 2'
  pigs-status
  pigs-checkout b1 
  ls -1
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test06_4(pigs-checkout change but not commit): Passed"
else
  echo "Test06_4(pigs-checkout change but not commit): failed"
fi



