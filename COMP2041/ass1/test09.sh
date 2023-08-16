#!/bin/dash


PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-init
  echo "hello COMP2041" > a.txt
  2041 pigs-add a.txt
  2041 pigs-commit -m root
  2041 pigs-branch branch_1
  2041 pigs-branch branch_2
  2041 pigs-checkout branch_1
  echo 0 > b.txt
  2041 pigs-add  b.txt
  2041 pigs-commit -m "test1"
  2041 pigs-checkout branch_2
  echo 1 > b.txt
  2041 pigs-add b.txt
  2041 pigs-commit -m "test2"
  2041 pigs-checkout branch_1
  2041 pigs-branch branch_3
  2041 pigs-branch branch_4
  2041 pigs-checkout branch_2
  2041 pigs-branch branch_5
  2041 pigs-branch branch_6
  2041 pigs-checkout branch_3
  ls -1
  2041 pigs-log
  echo "hello COMP2041 111" > c.txt
  2041 pigs-status
  2041 pigs-add c.txt
  2041 pigs-commit -m "test3"
  2041 pigs-checkout branch_4
  ls -1
  2041 pigs-log
  echo "~hello COMP2041~" > c.txt
  2041 pigs-add c.txt
  2041 pigs-commit -m "test4"
  2041 pigs-checkout branch_5
  ls -1
  2041 pigs-log
  echo "hello" > c.txt
  2041 pigs-add c.txt
  2041 pigs-status
  2041 pigs-commit -m "test"
  2041 pigs-checkout branch_6
  echo "hello COMP2041 121212121" > c.txt
  2041 pigs-add c.txt
  2041 pigs-commit -m "test"
  2041 pigs-checkout master
  ls -1
  2041 pigs-log
  2041 pigs-merge branch_1 -m "merge branch 1"
  ls -1
  cat a.txt
  cat b.txt
  cat c.txt
  2041 pigs-merge branch_3 -m "merge branch 3"
  cat a.txt
  cat b.txt
  cat c.txt
  ls -1
  2041 pigs-log
  2041 pigs-status
  2041 pigs-rm a
  ls -1
  2041 pigs-status
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  echo "hello COMP2041" > a.txt
  pigs-add a.txt
  pigs-commit -m root
  pigs-branch branch_1
  pigs-branch branch_2
  pigs-checkout branch_1
  echo 0 > b.txt
  pigs-add  b.txt
  pigs-commit -m "test1"
  pigs-checkout branch_2
  echo 1 > b.txt
  pigs-add b.txt
  pigs-commit -m "test2"
  pigs-checkout branch_1
  pigs-branch branch_3
  pigs-branch branch_4
  pigs-checkout branch_2
  pigs-branch branch_5
  pigs-branch branch_6
  pigs-checkout branch_3
  ls -1
  pigs-log
  echo "hello COMP2041 111" > c.txt
  pigs-status
  pigs-add c.txt
  pigs-commit -m "test3"
  pigs-checkout branch_4
  ls -1
  pigs-log
  echo "~hello COMP2041~" > c.txt
  pigs-add c.txt
  pigs-commit -m "test4"
  pigs-checkout branch_5
  ls -1
  pigs-log
  echo "hello" > c.txt
  pigs-add c.txt
  pigs-status
  pigs-commit -m "test"
  pigs-checkout branch_6
  echo "hello COMP2041 121212121" > c.txt
  pigs-add c.txt
  pigs-commit -m "test"
  pigs-checkout master
  ls -1
  pigs-log
  pigs-merge branch_1 -m "merge branch 1"
  ls -1
  cat a.txt
  cat b.txt
  cat c.txt
  pigs-merge branch_3 -m "merge branch 3"
  cat a.txt
  cat b.txt
  cat c.txt
  ls -1
  pigs-log
  pigs-status
  pigs-rm a
  ls -1
  pigs-status
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test09(Mixed test): Passed"
else
  echo "Test09(Mixed test): failed"
fi