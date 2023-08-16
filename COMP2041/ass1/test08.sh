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
  ls -1
  echo "Hello World" > file1.txt
  touch b
  2041 pigs-add b file1.txt
  ls -1
  cat file1.txt
  2041 pigs-commit -m "Added file1.txt"
  2041 pigs-status
  2041 pigs-log 
  2041 pigs-branch new_branch
  2041 pigs-checkout new_branch
  2041 pigs-branch
  echo "Hello from new_branch" > file2.txt
  2041 pigs-add file2.txt
  2041 pigs-commit -m "Added file2.txt in new_branch"
  ls -1
  cat file2.txt
  2041 pigs-status
  2041 pigs-log
  2041 pigs-checkout master
  2041 pigs-branch
  2041 pigs-merge new_branch -m "merge"
  2041 pigs-status
  2041 pigs-log
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  ls -1
  echo "Hello World" > file1.txt
  touch b
  pigs-add b file1.txt
  ls -1
  cat file1.txt
  pigs-commit -m "Added file1.txt"
  pigs-status
  pigs-log 
  pigs-branch new_branch
  pigs-checkout new_branch
  pigs-branch
  echo "Hello from new_branch" > file2.txt
  pigs-add file2.txt
  pigs-commit -m "Added file2.txt in new_branch"
  ls -1
  cat file2.txt
  pigs-status
  pigs-log
  pigs-checkout master
  pigs-branch
  pigs-merge new_branch -m "merge"
  pigs-status
  pigs-log
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test08(Mixed test): Passed"
else
  echo "Test08(Mixed test): failed"
fi