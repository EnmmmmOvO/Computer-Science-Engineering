#!/bin/dash

# Test 05: Branch (include error and normal test)
PATH=$PATH:$(pwd)
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)
result1=$(mktemp)
result2=$(mktemp)
trap 'rm -rf "$tmp1" "$tmp2" "result1" "result2"' EXIT

{
  cd "$tmp1" || exit
  2041 pigs-branch
  echo "$?"
  2041 pigs-init
  2041 pigs-branch
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-branch
  echo "$?"
  pigs-init
  pigs-branch
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_0(pigs-branch no argument error): Passed"
else
  echo "Test05_0(pigs-branch no argument error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m test
  2041 pigs-branch b1
  2041 pigs-branch b2
  2041 pigs-branch
  echo "$?"
  2041 pigs-branch -d b1
  2041 pigs-branch
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m test
  pigs-branch b1
  pigs-branch b2
  pigs-branch
  echo "$?"
  pigs-branch -d b1
  pigs-branch
  echo "$?"
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_1(pigs-branch no argument test): Passed"
else
  echo "Test05_1(pigs-branch no argument test): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-branch test
  echo "$?"
  2041 pigs-init
  2041 pigs-branch test
  echo "$?"
  touch a
  2041 pigs-add a
  2041 pigs-commit -m test
  2041 pigs-branch test1
  2041 pigs-branch -d
  echo "$?"
  2041 pigs-branch test1
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-branch test
  echo "$?"
  pigs-init
  pigs-branch test
  echo "$?"
  touch a
  pigs-add a
  pigs-commit -m test
  pigs-branch test1
  pigs-branch -d
  echo "$?"
  pigs-branch test1
  echo "$?"
} > "$result2" 2>&1


if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_2(pigs-branch one argument error): Passed"
else
  echo "Test05_2(pigs-branch one argument error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)


{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m test
  2041 pigs-branch test1
  2041 pigs-checkout test1
  2041 pigs-status
  ls -1
  2041 pigs-branch test2
  2041 pigs-checkout test2
  2041 pigs-status
  ls -1
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m test
  pigs-branch test1
  pigs-checkout test1
  pigs-status
  ls -1
  pigs-branch test2
  pigs-checkout test2
  pigs-status
  ls -1
} > "$result2" 2>&1

diff "$result1" "$result2"
if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_3(pigs-branch one argument test): Passed"
else
  echo "Test05_3(pigs-branch one argument test): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-branch -d test1
  echo "$?"
  2041 pigs-init
  2041 pigs-branch -d test1
  echo "$?"
  2041 pigs-branch -d master
  echo "$?"
  2041 pigs-add a
  2041 pigs-commit -m test
  2041 pigs-branch -d test1
  echo "$?"
  2041 pigs-branch -d master
  echo "$?"
  2041 pigs-branch test1
  2041 pigs-checkout test1
  2041 pigs-branch -d test1
  echo "$?"
  2041 pigs-branch -d test1 ete
  echo "$?"
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-branch -d test1
  echo "$?"
  pigs-init
  pigs-branch -d test1
  echo "$?"
  pigs-branch -d master
  echo "$?"
  pigs-add a
  pigs-commit -m test
  pigs-branch -d test1
  echo "$?"
  pigs-branch -d master
  echo "$?"
  pigs-branch test1
  pigs-checkout test1
  pigs-branch -d test1
  echo "$?"
  pigs-branch -d test1 ete
  echo "$?"
} > "$result2" 2>&1


if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_4(pigs-branch two argument error): Passed"
else
  echo "Test05_4(pigs-branch two argument error): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  2041 pigs-branch
  2041 pigs-branch b2
  2041 pigs-branch -d b1
  echo "$?"
  2041 pigs-branch
  2041 pigs-branch -d b2
  echo "$?"
  2041 pigs-branch
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m 'test'
  pigs-branch b1
  pigs-checkout b1
  pigs-branch
  pigs-branch b2
  pigs-branch -d b1
  echo "$?"
  pigs-branch
  pigs-branch -d b2
  echo "$?"
  pigs-branch
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_5(pigs-branch two argument test): Passed"
else
  echo "Test05_5(pigs-branch two argument test): failed"
fi
rm -rf "$tmp1" "$tmp2"
tmp1=$(mktemp -d)
tmp2=$(mktemp -d)

{
  cd "$tmp1" || exit
  2041 pigs-init
  touch a
  2041 pigs-add a
  2041 pigs-commit -m 'test'
  2041 pigs-branch b1
  2041 pigs-checkout b1
  touch b
  2041 pigs-add a
  2041 pigs-commit -m 'b'
  2041 pigs-checkout master
  2041 pigs-branch -d b1
  echo "$?"
  2041 pigs-merge b1 -m merge
  2041 pigs-branch -d b1
  echo "$?"
  2041 pigs-branch
} > "$result1" 2>&1

{
  cd "$tmp2" || exit
  pigs-init
  touch a
  pigs-add a
  pigs-commit -m 'test'
  pigs-branch b1
  pigs-checkout b1
  touch b
  pigs-add a
  pigs-commit -m 'b'
  pigs-checkout master
  pigs-branch -d b1
  echo "$?"
  pigs-merge b1 -m merge
  pigs-branch -d b1
  echo "$?"
  pigs-branch
} > "$result2" 2>&1

if diff "$result1" "$result2" > /dev/null; then
  echo "Test05_6(pigs-branch two argument delete unmerge branch): Passed"
else
  echo "Test05_6(pigs-branch two argument delete unmerge branch): failed"
fi
