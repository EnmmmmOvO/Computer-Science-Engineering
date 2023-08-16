#!/bin/dash


PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-merge
  echo "$?"
  2041 pigs-init
  2041 pigs-merge
  touch a
  2041 pigs-add a
  2041 pigs-commit -m 'test1'
  2041 pigs-merge a
  echo "$?"
  2041 pigs-merge a m s
  echo "$?"
  2041 pigs-merge no-brance -m s
  echo "$?"
  2041 pigs-merge no-brance -s s
  echo "$?"
  2041 pigs-branch b1
  echo ssss > a
  2041 pigs-commit -a -m 'test2'
  2041 pigs-checkout b1
  echo llll > a
  2041 pigs-commit -a -m 'test2'
  2041 pigs-merge master -m "err"
  echo "$?"
  2041 pigs-log
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-merge
  echo "$?"
  pigs-init
  pigs-merge
  touch a
  pigs-add a
  pigs-commit -m 'test1'
  pigs-merge a
  echo "$?"
  pigs-merge a m s
  echo "$?"
  pigs-merge no-brance -m s
  echo "$?"
  pigs-merge no-brance -s s
  echo "$?"
  pigs-branch b1
  echo ssss > a
  pigs-commit -a -m 'test2'
  pigs-checkout b1
  echo llll > a
  pigs-commit -a -m 'test2'
  pigs-merge master -m "err"
  echo "$?"
  pigs-log
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_0(pigs-merge error): Passed"
else
  echo "Test07_0(pigs-merge error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo test > a
  echo test > b
  echo test > c
  2041 pigs-add a b c
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  echo "a test" > a
  echo "b test" > b
  echo "c test" > c
  2041 pigs-commit -a -m 'test1'
  2041 pigs-checkout b1
  echo "b1 a test" > a
  echo "b1 b test" > b
  echo "b1 c test" > c
  2041 pigs-commit -a -m 'test1'
  2041 pigs-merge master -m "test"
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo test > a
  echo test > b
  echo test > c
  pigs-add a b c
  pigs-commit -m 'test'
  pigs-branch b1
  echo "a test" > a
  echo "b test" > b
  echo "c test" > c
  pigs-commit -a -m 'test1'
  pigs-checkout b1
  echo "b1 a test" > a
  echo "b1 b test" > b
  echo "b1 c test" > c
  pigs-commit -a -m 'test1'
  pigs-merge master -m "test"
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_1(pigs-merge more than one file merge error): Passed"
else
  echo "Test07_1(pigs-merge more than one file merge error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "hello I am COMP2041 student" > a
  2041 pigs-add a
  2041 pigs-commit -m commit-1
  2041 pigs-branch b1
  2041 pigs-checkout b1
  echo "I am UNSW student" > a
  2041 pigs-commit -a -m commit-2
  2041 pigs-checkout master
  cat a
  2041 pigs-merge b1 -m merge-message
  cat a
  2041 pigs-log
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "hello I am COMP2041 student" > a
  pigs-add a
  pigs-commit -m commit-1
  pigs-branch b1
  pigs-checkout b1
  echo "I am UNSW student" > a
  pigs-commit -a -m commit-2
  pigs-checkout master
  cat a
  pigs-merge b1 -m merge-message
  cat a
  pigs-log
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_2(pigs-merge Fast forward): Passed"
else
  echo "Test07_2(pigs-merge Fast forward): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo test > a
  echo test > b
  echo test > c
  2041 pigs-add a b c
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  echo "b1 a test" > a
  echo "b1 b test" > b
  echo "b1 c test" > c
  2041 pigs-commit -a -m 'test1'
  2041 pigs-merge master -m "test"
  echo "$?"
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo test > a
  echo test > b
  echo test > c
  pigs-add a b c
  pigs-commit -m 'test'
  pigs-branch b1
  pigs-checkout b1
  echo "b1 a test" > a
  echo "b1 b test" > b
  echo "b1 c test" > c
  pigs-commit -a -m 'test1'
  pigs-merge master -m "test"
  echo "$?"
  ls -1
} > "$result2" 2>&1

 diff "$result1" "$result2"
if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_3(pigs-merge Already up to date): Passed"
else
  echo "Test07_3(pigs-merge Already up to date): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo test > a
  echo test > b
  2041 pigs-add a b
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  echo "test a, hello" > a
  2041 pigs-commit -a -m 'test2'
  2041 pigs-checkout b1
  cat a
  ls -1
  echo "test b, hello" > b
  2041 pigs-commit -a -m 'test2'
  2041 pigs-checkout master
  cat b
  ls -1
  2041 pigs-merge b1 -m 'merge'
  cat a
  cat b
  ls -1
  2041 pigs-log
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo test > a
  echo test > b
  pigs-add a b
  pigs-commit -m 'test'
  pigs-branch b1
  echo "test a, hello" > a
  pigs-commit -a -m 'test2'
  pigs-checkout b1
  cat a
  ls -1
  echo "test b, hello" > b
  pigs-commit -a -m 'test2'
  pigs-checkout master
  cat b
  ls -1
  pigs-merge b1 -m 'merge'
  cat a
  cat b
  ls -1
  pigs-log
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_4(pigs-merge merge with commit1): Passed"
else
  echo "Test07_4(pigs-merge merge with commit1): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo test > a
  echo test > b
  2041 pigs-add a b
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  echo "test a, hello" > a
  2041 pigs-commit -a -m 'test2'
  2041 pigs-checkout b1
  echo "test b, hello" > b
  2041 pigs-commit -a -m 'test2'
  2041 pigs-merge master -m 'merge'
  2041 pigs-log
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo test > a
  echo test > b
  pigs-add a b
  pigs-commit -m 'test'
  pigs-branch b1
  echo "test a, hello" > a
  pigs-commit -a -m 'test2'
  pigs-checkout b1
  echo "test b, hello" > b
  pigs-commit -a -m 'test2'
  pigs-merge master -m 'merge'
  pigs-log
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test07_5(pigs-merge parent log test): Passed"
else
  echo "Test07_5(pigs-merge parent log test): failed"
fi