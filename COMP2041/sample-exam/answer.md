### Question 1 (10 marks)



You have been given the file `awards.psv`

This file contains information about Nobel Prize, Turing Award and Fields Medal winners

Each line in the file contains the following six fields:

1. Award Name
2. Award Year
3. Winner Name
4. Winner Gender
5. Winner Country
6. Winner Birth Year

Each field is separated from the next field by a pipe character (`|`).

Your task is to write four [grep](https://manpages.debian.org/jump?q=grep.1) commands which will print specified lines from this file.

You have been given the file `practice_q1.txt`.

In `practice_q1.txt` add answers to the four questions.

Add each answer in the specified location.

Do not add, remove, or change any other text in the file.

The autotest depends on the exact format of the file.

Each question should be answered with a single [grep](https://manpages.debian.org/jump?q=grep.1) command.

You may use any regular expression syntax supported by [grep](https://manpages.debian.org/jump?q=grep.1).

You may use any options supported by [grep](https://manpages.debian.org/jump?q=grep.1) except `-P/--perl-regexp`.

1. **Question 1**

   Write a [grep](https://manpages.debian.org/jump?q=grep.1) command that will print the lines in `awards.psv` that contain awards won by an Australian.

2. **Question 2**

   Write a [grep](https://manpages.debian.org/jump?q=grep.1) command that will print the lines in `awards.psv` that contain a female ACM Turing Award winner.

3. **Question 3**

   Write a [grep](https://manpages.debian.org/jump?q=grep.1) command that will print the lines in `awards.psv` that contain Nobel Prizes won by a person born between 1990 and 1999 (inclusive).

4. **Question 4**

   Write a [grep](https://manpages.debian.org/jump?q=grep.1) command that will print the lines in `awards.psv` that contain awards won by a person with first name, last name, and middle initial starting with the same letter.

Your example to each question will be a single grep command.

You can test the command by running it in the terminal.

For example, if you think the answer to question 1 is `grep -E 'Andrew' awards.psv`,
you can test it:



```
grep -E 'Andrew' awards.psv
ACM Turing Award|2000|Andrew Chi-Chih Yao|Male|China|1946
Nobel Prize for medicine|1963|Andrew F. Huxley|Male|United Kingdom|1917
Nobel Prize for medicine|2006|Andrew Z. Fire|Male|United States|1959
Nobel Prize for medicine|1977|Andrew V. Schally|Male|United States|1926
ACM Turing Award|2017|David Andrew Patterson|Male|United States|1947
```

Then add it to `practice_q1.txt`.

Autotest will extract your answers from `practice_q1.txt` and do a simple test.

- Your answer for each question **must** be a single [grep](https://manpages.debian.org/jump?q=grep.1) command only
  For example: `grep -E Andrew awards.psv`
- You **may not** use the `-P/--perl-regexp` option to grep
- You **may** use any other [grep](https://manpages.debian.org/jump?q=grep.1) option, for example you can use grep's `-w` option.
- You **may** quote the arguments to grep.
- You **may not** use any commands other than [grep](https://manpages.debian.org/jump?q=grep.1), for example, you can not use [sed](https://manpages.debian.org/jump?q=sed.1) or cut(1).
- You **can not** use pipes, or I/O redirection.
- You **can** assume that the pipe character (`|`) will only appear as a field separator.
- Note the **input is unordered**.
  It is not sorted in any way.
- You **may not** use `Shell`, `C`, `Python`, `Perl`, or any other language.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q1
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q1 practice_q1.txt
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q1.txt`

```
This file is automarked.

Do not add extra lines to this file, just add your answers.

For example if your answer to Q0 is: "grep -E Andrew awards.psv"
Change the line that starts with

    "Q0 answer:"
to
    "Q0 answer: grep -E Andrew awards.psv"

You may add comments to your answers in the following format:

Q0 answer: grep -E Andrew awards.psv
# This is a comment
# This is another comment

That is the comment must immediately follow the answer and start with a '#' character.

------------------------------------------------------------------------------------------------------------------------

1) Australian winners
Q1 answer: grep -F '|Australia|' awards.psv
# Use -F (fixed string) to as we don't actually need regex for this question
# Assume that nobody has the name "Australia"

------------------------------------------------------------------------------------------------------------------------

2) Female, ACM Turing Award, winners
Q2 answer: grep -xE 'ACM Turing Award\|[^|]+\|[^|]+\|Female\|[^|]+\|[^|]+' awards.psv
# Use -x (match entire line)
# pipe characters needs to be escaped '\|' as it is a special character in regex
# use '[^|]+' for a non-greedy match as grep -E doesn't have '[^|]+?'

------------------------------------------------------------------------------------------------------------------------

3) Nobel Prize winners born between 1990 and 1999
Q3 answer: grep -xE 'Nobel Prize [^|]+\|[^|]+\|[^|]+\|[^|]+\|[^|]+\|199[0-9]' awards.psv
# Use -x (match entire line)
# pipe characters needs to be escaped '\|' as it is a special character in regex
# use '[^|]+' for a non-greedy match as grep -E doesn't have '[^|]+?'

------------------------------------------------------------------------------------------------------------------------

4) winners with first name, last name, and middle initial starting with the same letter
Q4 answer: grep -E '^[^|]+\|[^|]+\|(.)[^|]+ \1\. \1[^|]+\|' awards.psv
# Use (.) to capture the first letter
# Then use \1 to refer to this capture
```

### Question 2 (9 marks)



We have student enrolment data in this familiar format:

```
cat enrollments.txt
COMP1511|3360379|Costner, Kevin Augustus          |3978/1|M
COMP1511|3364562|Carey, Mary                      |3711/1|M
COMP3311|3383025|Thorpe, Ian Augustus             |3978/3|M
COMP4920|3860448|Steenburgen, Mary Nell           |3978/3|F
COMP1521|3360582|Neeson, Liam                     |3711/2|M
COMP3411|3863711|Klum, Heidi June Anne            |3978/3|F
COMP3141|3383025|Thorpe, Ian Augustus             |3978/3|M
COMP3891|3863711|Klum, Heidi June Anne            |3978/3|F
COMP3331|3383025|Thorpe, Ian Augustus             |3978/3|M
COMP2041|3860448|Steenburgen, Mary Nell           |3978/3|F
COMP2041|3360582|Neeson, Liam                     |3711/2|M
COMP3311|3711611|Klum, Mary                       |3978/3|F
COMP3311|3371161|Thorpe, Ian Fredrick             |3711/3|M
COMP3331|5122456|Wang, Wei                        |3978/2|M
COMP3331|5456732|Wang, Wei                        |3648/3|M
COMP4920|5456732|Wang, Wei                        |3648/3|M
```

You should find a copy of the above data in the provided file **enrollments.txt**.

Each line in the file contains the following five fields:

1. UNSW Course Code
2. Student ID Number
3. Student Name (surname(s), given-names(s))
4. Student Plan
5. Student Gender

Each field is separated from the next field by a pipe character (`|`).

In **practice_q2.sh**, write a shell pipeline that,
given student enrollment data, on stdin, in the above format,
will output the **surnames** (family names) of **male** students.

Each surname should be printed only once

The surnames should be printed in alphabetical order.

The input is unordered.
In other words it is not sorted in any way.

The last field contains **M** if a student identifies as **male**.

A **comma** separates the surname(s) from the given-name(s).

For example, given the above data, your pipeline should output this:

```
./practice_q2.sh < enrollments.txt
Carey
Costner
Neeson
Thorpe
Wang
```

Using the additional data file provided,
your pipeline should output this:

```
./practice_q2.sh < more_enrollments.txt
Bai
Bian
Cai
Cui
Guo
Islam
Kumar
Li
Long
Lu
Luong
Luu
Murray
Ngo
Saha
Tran
Trinh
Wu
Xia
Xiao
Yao
Ye
Yip
Yong
Zeng
```

- You **may** assume that the data always has 5 fields.

- Your answer **must** be a single Shell pipeline.

- Your pipeline **should** take input from standard input.

- Your shell pipeline **should** be placed in the file `practice_q2.sh`
  For example, if your answer to this question is:

  ```
  grep "Andrew" | sed 's/^/Hello/' | sort
  ```

  then

   

  ```
  practice_q2.sh
  ```

   

  should contain:

  ```
  cat practice_q2.sh
  #! /bin/dash
  grep "Andrew" | sed 's/^/Hello/' | sort
  ```

- You **may** use the standard UNIX filters, including: [cut](https://manpages.debian.org/jump?q=cut.1), [grep](https://manpages.debian.org/jump?q=grep.1), [head](https://manpages.debian.org/jump?q=head.1), [sed](https://manpages.debian.org/jump?q=sed.1), [sort](https://manpages.debian.org/jump?q=sort.1), [tail](https://manpages.debian.org/jump?q=tail.1), [uniq](https://manpages.debian.org/jump?q=uniq.1), [wc](https://manpages.debian.org/jump?q=wc.1), Etc.

- You **may not** use `if`, `while`, `for`, or other shell syntax.

- You **may not** use `&&`, `||`, `;`, or other shell syntax.

- You **may not** use `Perl`, `C`, `Python`, or any other language.

- You **may not** use `awk`.

- You **may not** create temporary files.

- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q2
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q2 practice_q2.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q2.sh`

```
#! /usr/bin/env dash

grep '|M$'         \
  | cut -d'|' -f3  \
  | cut -d',' -f1  \
  | sort           \
  | uniq           \

# grep for all lines ending with 'M'
# cut the third field using '|' as the delimiter (the third field is student name)
# cut the first field using ',' as the delimiter (the first field is student surname)
# sort the names and remove duplicates
```

### Question 3 (9 marks)



Write a Python program **practice_q3.py** that performs the same task as the Shell pipeline in the previous question.

In other words: given data in the same format as the last question on standard input,
output the surnames (family names) of **male** students.

Each surname should be printed only once

The surnames should be printed in alphabetical order.

For example:

```
./practice_q3.py < enrollments.txt
Carey
Costner
Neeson
Thorpe
Wang
```

- Your program **should** read input from standard input.
- Your answer **must** be `Python` only.
- You **may not** use `Shell`, `C`, `Perl`, or any other language.
- You **may not** run external programs, e.g. via the `subprocess` module, or any other method.
- You **may** `import` any other standard `Python` module installed at CSE.
- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q3
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q3 practice_q3.py
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q3.py`

```
#! /usr/bin/env python3

import sys

surnames = set()

for line in sys.stdin:
    _, _, name, _, gender = line.strip().split("|")
    if gender == "M":
        surname = name.split(",")[0]
        surnames.add(surname)

print("\n".join(sorted(surnames)))
```

### Question 4 (8 marks)



Write a POSIX-compatible shell script `./practice_q4.sh` that takes a single command-line argument, a filename.

The file will contain an unordered list of positive integers, one per line, from n to m, with possibly one integer missing.

Your shell script should print the missing integer, if there is a missing integer.

If there is no missing integer your script should print nothing.

No integer will occur twice.

At most one integer will be missing.

The missing integer will not be n or m.

For example, `./practice_q4.sh` should output this:

```
cat numbers_1.txt
39
45
40
44
41
43
./practice_q4.sh numbers_1.txt
42
cat numbers_2.txt
6
8
9
1
7
2
3
10
11
12
5
./practice_q4.sh numbers_2.txt
4
./practice_q4.sh numbers_3.txt
1005
./practice_q4.sh numbers_4.txt
```

- You can assume there is always exactly one command-line argument, a valid filename.
- You can assume the file contains only positive integers, one per line.
- You can assume there will be at least two integers in the file.
- You can *not* assume that there will always be a missing integer.
- You can assume that at most one integer integer is missing.
- Your script should produce at most 1 line of output.
- You **are** permitted to create temporary files.
- You are permitted to use these and only these external programs:
  - [basename](https://manpages.debian.org/jump?q=basename.1)
  - [cat](https://manpages.debian.org/jump?q=cat.1)
  - [chmod](https://manpages.debian.org/jump?q=chmod.1)
  - [cmp](https://manpages.debian.org/jump?q=cmp.1)
  - [cp](https://manpages.debian.org/jump?q=cp.1)
  - [cut](https://manpages.debian.org/jump?q=cut.1)
  - [diff](https://manpages.debian.org/jump?q=diff.1)
  - [dirname](https://manpages.debian.org/jump?q=dirname.1)
  - [echo](https://manpages.debian.org/jump?q=echo.1)
  - [expr](https://manpages.debian.org/jump?q=expr.1)
  - [false](https://manpages.debian.org/jump?q=false.1)
  - [find](https://manpages.debian.org/jump?q=find.1)
  - [grep](https://manpages.debian.org/jump?q=grep.1)
  - [head](https://manpages.debian.org/jump?q=head.1)
  - [ls](https://manpages.debian.org/jump?q=ls.1)
  - [mkdir](https://manpages.debian.org/jump?q=mkdir.1)
  - [mktemp](https://manpages.debian.org/jump?q=mktemp.1)
  - [mv](https://manpages.debian.org/jump?q=mv.1)
  - [printf](https://manpages.debian.org/jump?q=printf.1)
  - [pwd](https://manpages.debian.org/jump?q=pwd.1)
  - [rev](https://manpages.debian.org/jump?q=rev.1)
  - [rm](https://manpages.debian.org/jump?q=rm.1)
  - [rmdir](https://manpages.debian.org/jump?q=rmdir.1)
  - [sed](https://manpages.debian.org/jump?q=sed.1)
  - [seq](https://manpages.debian.org/jump?q=seq.1)
  - [sort](https://manpages.debian.org/jump?q=sort.1)
  - [stat](https://manpages.debian.org/jump?q=stat.1)
  - [strings](https://manpages.debian.org/jump?q=strings.1)
  - [tac](https://manpages.debian.org/jump?q=tac.1)
  - [tail](https://manpages.debian.org/jump?q=tail.1)
  - [tee](https://manpages.debian.org/jump?q=tee.1)
  - [test](https://manpages.debian.org/jump?q=test.1)
  - [touch](https://manpages.debian.org/jump?q=touch.1)
  - [tr](https://manpages.debian.org/jump?q=tr.1)
  - [true](https://manpages.debian.org/jump?q=true.1)
  - [uniq](https://manpages.debian.org/jump?q=uniq.1)
  - [wc](https://manpages.debian.org/jump?q=wc.1)
  - [xargs](https://manpages.debian.org/jump?q=xargs.1)
- You are permitted to use any built-in shell features including:
  - `case`
  - `cd`
  - `exit`
  - `for`
  - `if`
  - `read`
  - `shift`
  - `while`
- You may not use non-POSIX-compatible Shell.
  You are not permitted to use `/bin/bash` or `/bin/sh`.
  You can assume anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.
- You **may not** use `Perl`, `C`, `Python`, or any other language.
- You **may not** use `awk`.
- No error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q4
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q4 practice_q4.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q4.sh`

```
#! /usr/bin/env dash

seq "$(sort -n "$1" | sed 1q)" "$(sort -nr "$1" | sed 1q)" \
  | grep -Exvf  "$1"
```

### Question 5 (8 marks)



In **question 1** you were given the file `awards.psv`

containing information about Nobel Prizes, Turing Awards and Fields Medal winners

This time we are interested in the years particular awards were not given, between when it was first offered and when it was last offered.

Write a POSIX-compatible Shell script **practice_q5.sh** that prints all years that an award was not given in.

**practice_q5.sh** will be given two command-line arguments, a regular expression and a file name,
**practice_q5.sh** should print in sorted order the years that no award whose **entire**name matches the regex given.

The entire name must match the regex not just a substring.

For example if the regex is `Nobel Prize`, then awards for `Nobel Prize for physics` should not match.
But if the regex is `Nobel Prize.*`, then awards for `Nobel Prize for physics` should match.

You should not hard code the name of this file in your script, the name of the data file will be given as the second command-line argument.

If there are no awards that match the regex, then **practice_q5.sh** should print an message to stdout as below.

For example, the Nobel prize for physics was first awarded in 1901 and last awarded in 2021.
It was not awarded in these six years:

```
./practice_q5.sh 'Nobel Prize for physics' awards.psv
1916
1931
1934
1940
1941
1942
```

More example output:

```
./practice_q5.sh 'Nobel Prize for (chemistry|physics)' awards.psv
1916
1940
1941
1942
./practice_q5.sh 'Nobel Prize for.*' awards.psv
1940
1941
1942
./practice_q5.sh 'COMP2041 Distinguished Achievers' awards.psv
No award matching 'COMP2041 Distinguished Achievers'
```

- You **can** assume that the pipe character (`|`) will only appear as a field separator.

- Note the input is unordered. It is not sorted in any way.

- You are **only** permitted to use these external programs:

  - `basename`
  - `cat`
  - `chmod`
  - `cmp`
  - `cp`
  - `cut`
  - `diff`
  - `dirname`
  - `echo`
  - `expr`
  - `false`
  - `find`
  - `grep`
  - `head`
  - `ls`
  - `mkdir`
  - `mv`
  - `printf`
  - `pwd`
  - `rev`
  - `rm`
  - `rmdir`
  - `sed`
  - `seq`
  - `sort`
  - `stat`
  - `strings`
  - `tac`
  - `tail`
  - `tee`
  - `test`
  - `touch`
  - `tr`
  - `true`
  - `uniq`
  - `wc`
  - `xargs`

  See `man 1 <program>` for more info on any program

- You are permitted to use **any** POSIX-compatible built-in shell features including:

  - `case`
  - `cd`
  - `exit`
  - `for`
  - `if`
  - `read`
  - `shift`
  - `while`

  See `man 1 dash` for more info on any built-in

  See `help <built-in>` for *bash* info on any built-in (might not be POSIX-compatible)

- You **may not** use non-POSIX-compatible shell features.
  You **are not permitted** to use `/bin/bash`, `/bin/sh`, or any other shell.
  Make the first line of your shell-script `#!/bin/dash`
  You **can** assume that anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.

- You **may not** use `Perl`, `C`, `Python`, `awk` or any language other than shell.

- You **may not** create temporary files.

- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q5
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q5 practice_q5.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q5.sh`

```
#! /usr/bin/env dash

# Given
# 1) a 'pipe seperated values' file with award winners
# in the format:
#   award name
#   award year
#   winner name
#   winner gender
#   winner country
#   winner birth year
# 2) The name of an award
#
# find all years in which the award was *not* given

years=$(grep -E "^$1\|" "$2" | sort -t'|' -k2 | cut -d'|' -f2)

if [ -z "$years" ]; then
    echo "No award matching '$1'" >&2
    exit 1
fi

start=$(echo "$years" | head -n1)
end=$(echo "$years" | tail -n1)

for year in $(seq "$start" "$end"); do
    if ! echo "$years" | grep -q "$year"; then
        echo "$year"
    fi
done
```

Alternative solution for `practice_q5.sh`

```
#! /usr/bin/env dash

# Use comm instead of a for loop with grep
# Requires the use of a temporary file
# (Not a valid solution as not allowed to make use of a temporary file)

# Given
# 1) a 'pipe seperated values' file with award winners
# in the format:
#   award name
#   award year
#   winner name
#   winner gender
#   winner country
#   winner birth year
# 2) The name of an award
#
# find all years in which the award was *not* given

years=$(grep -E "^$1\|" "$2" | sort -t'|' -k2 | cut -d'|' -f2)

if [ -z "$years" ]; then
    echo "No award matching '$1'" >&2
    exit 1
fi

start=$(echo "$years" | head -n1)
end=$(echo "$years" | tail -n1)

tmp=$(mktemp)
seq "$start" "$end" > "$tmp"
echo "$years" | comm -23 "$tmp" -
rm -f "$tmp"
```

Alternative solution for `practice_q5.sh`

```
#! /usr/bin/env bash

# Use process substitution instead of a temporary file
# Requires bash
# (Not a valid solution as not POSIX compliant)

# Given
# 1) a 'pipe seperated values' file with award winners
# in the format:
#   award name
#   award year
#   winner name
#   winner gender
#   winner country
#   winner birth year
# 2) The name of an award
#
# find all years in which the award was *not* given

years=$(grep -E "^$1\|" "$2" | sort -t'|' -k2 | cut -d'|' -f2)

if [ -z "$years" ]; then
    echo "No award matching '$1'" >&2
    exit 1
fi

start=$(echo "$years" | head -n1)
end=$(echo "$years" | tail -n1)

comm -23 <(seq "$start" "$end") <(echo "$years")
```

### Question 6 (8 marks)



Two files are **mirrored** if they contain the same lines but in the reverse order to each other.

Write a Python program **practice_q6.py** that given two filenames checks if the two files are **mirrored**.

**practice_q6.py** should always produce one line of output.

If the two files are **mirrored** **practice_q6.py** should print a message indicating this.

If the two files are not **mirrored** **practice_q6.py** should print a message indicating why not.

Match the example output below exactly:

If the two files contain a different number of lines,
**practice_q6.py** should print a single line indicating this, including the number of lines in each file.

This message should be printed in **exactly** the format below.

```
echo hello >file1
echo Andrew >>file1
echo Dylan >file2
cat file1
hello
Andrew
cat file2
Dylan
./practice_q6.py file1 file2
Not mirrored: different number of lines: 2 versus 1
./practice_q6.py file2 file1
Not mirrored: different number of lines: 1 versus 2
```

If the files contain the same number of lines but a line in the first file
is not the same as the corresponding line in the second file in reverse order,
**practice_q6.py** should print a single line indicating this.

The message should indicate the line number in the first file (only).

The message should be printed in **exactly** the format below.

```
echo hello >>file2
cat file1
hello
Andrew
cat file2
Dylan
hello
./practice_q6.py file1 file2
Not mirrored: line 2 different
./practice_q6.py file2 file1
Not mirrored: line 1 different
```

Note, message should only be for the first line which is different.
The example below shows files where multiple lines are different.

```
sed -i s/hello/hi/ file1
cat file1
hi
Andrew
cat file2
Dylan
hello
./practice_q6.py file1 file2
Not mirrored: line 1 different
./practice_q6.py file2 file1
Not mirrored: line 1 different
```

The example below shows **mirrored** files.

```
echo hello >file3
echo Dylan >>file3
cat file3
hello
Dylan
cat file2
Dylan
hello
./practice_q6.py file2 file3
Mirrored
seq 1 5 >a
seq 5 -1 1 >b
cat a
1
2
3
4
5
cat b
5
4
3
2
1
./practice_q6.py a b
Mirrored
```

- Your program should always produce exactly one line of output.
- Your program can assume it is given exactly two command-line arguments: the names of two files.
- You can assume all lines in the two files are terminated with a single '\n' byte.
- You can assume the two files contain only ASCII bytes.
- You may read all of both files before producing output.
- You can assume the files are small enough to fit in memory, e.g. the lines can be read into a list.
- Your answer **must** be `Python` only.
- You **may not** use `Shell`, `C`, `Perl`, or any other language.
- You **may not** run external programs, e.g. via the `subprocess` module, or any other method.
- You **may** `import` any other standard `Python` module installed at CSE.
- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q6
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q6 practice_q6.py
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q6.py`

```
#!/usr/bin/python3
import sys

with open(sys.argv[1]) as f:
    lines1 = f.readlines()

with open(sys.argv[2]) as f:
    lines2 = f.readlines()

different_line_numbers = [
    n for (n, (e1, e2)) in enumerate(zip(lines1, reversed(lines2)), start=1) if e1 != e2
]

if len(lines1) != len(lines2):
    print(f"Not mirrored: different number of lines: {len(lines1)} versus {len(lines2)}")
elif different_line_numbers:
    print(f"Not mirrored: line {different_line_numbers[0]} different")
else:
    print("Mirrored")
```

### Question 7 (8 marks)



We have many executable scripts which we want to rename with an extension if possible.

Reminder, a filename extension is a suffix on the end of a filename that indicates the file contents.
For example, an extension of **.sh** can be used to indicate a file contains a shell script.

Write a POSIX-compatible Shell script `practice_q7.sh` which given one or more filenames as command-line arguments,
prints shell commands to add extensions to the filenames.

We need to check the commands before executing them, so `practice_q7.sh` should **print the commands, not execute them**.

For each filename, `practice_q7.sh` should print one line of output to `stdout`,
matching the example output below **exactly**.

- If the filename already has an extension (contains a '.'),
  print a line indicating this.
- If the file does not start with **#!**,
  print a line indicating this.
- If the **#!** line does not contain any of the strings, **perl**, **python** or **sh**,
  print a line indicating this.
- If a file already exists with the new filename created by adding the appropriate extension,
  print a line indicating this.
- Otherwise, **practice_q7.sh** should print a line containing a command to rename the file.

The line printed for each filename should match the example output below **exactly**.
For example:

```
touch script.rs
./practice_q7.sh script.rs
# script.rs already has an extension
./practice_q7.sh script1
# script1 does not have a #! line
./practice_q7.sh script2
# script2 no extension for #! line
practice_q7.sh script3
mv script3 script3.py
./practice_q7.sh script*
# script1 does not have a #! line
# script2 no extension for #! line
mv script3 script3.py
mv script4 script4.pl
mv script5 script5.sh
touch script4.pl
./practice_q7.sh script4
# script4.pl already exists
```

- A **#!** line must be the first line in a file.

- Do not examine other lines in the files.

- Do not assume anything about the format of **#!** lines.

- If the string **python** appears anywhere in a **#!** line, the appropriate suffix for the file is **.py**

- If the string **perl** appears anywhere in a **#!** line, the appropriate suffix for the file is **.pl**

- If the string **sh** appears anywhere in a **#!** line, the appropriate suffix for the file is **.sh**

- Your program should only add **.sh**, **.pl** and **.py** extensions.
  It should not add other extensions.
  It should instead print the message shown in the example output.

- Your program should not actually rename the files.

  It should only print the command to stdout.

- Your program can assume the filenames it is given exist.

- You can assume filenames contain only letters, digits and the characters '.' and '_'.

- You are **only** permitted to use these external programs:

  - `basename`
  - `cat`
  - `chmod`
  - `cmp`
  - `cp`
  - `cut`
  - `diff`
  - `dirname`
  - `expr`
  - `false`
  - `find`
  - `grep`
  - `head`
  - `ls`
  - `mkdir`
  - `mv`
  - `printf`
  - `pwd`
  - `rev`
  - `rm`
  - `rmdir`
  - `sed`
  - `seq`
  - `sort`
  - `stat`
  - `strings`
  - `tac`
  - `tail`
  - `tee`
  - `test`
  - `touch`
  - `tr`
  - `true`
  - `uniq`
  - `wc`
  - `xargs`

  See `man 1 <program>` for more info on any program

- You are permitted to use **any** built-in shell features including:

  - `cd`
  - `echo`
  - `exit`
  - `for`
  - `if`
  - `case`
  - `read`
  - `shift`
  - `while`

  See `man 1 dash` for more info on any built-in

  See `help <built-in>` for *bash* info on any built-in (might not be POSIX-compatible)

- You **may not** use non-POSIX-compatible shell features.
  You **are not permitted** to use `/bin/bash`, `/bin/sh`, or any other shell.
  Make the first line of your shell-script `#!/bin/dash`
  You **can** assume that anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.

- You **may not** use `Perl`, `C`, `Python`, `awk` or any language other than shell.

- You **may not** create temporary files.

- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q7
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q7 practice_q7.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q7.sh`

```
#! /usr/bin/env dash

for pathname in "$@"; do

    case "$(head -1 "$pathname")" in
        *perl*)   extension="pl" ;;
        *python*) extension="py" ;;
        *sh*)     extension="sh" ;;
        *)        extension=""   ;;
    esac

    new_pathname="$pathname.$extension"

    if echo "$pathname" | grep -Eq '\.[^/]+$'; then
        echo "# $pathname already has an extension"
    elif [ "$(head -c 2 "$pathname")" != '#!' ]; then
        echo "# $pathname does not have a #! line"
    elif [ -z "$extension" ]; then
        echo "# $pathname no extension for #! line"
    elif [ -e "$new_pathname" ]; then
        echo "# $new_pathname already exists"
    else
        echo "mv $pathname $new_pathname"
    fi

done
```

### Question 8 (8 marks)



We wish to save disk space by replacing identical copies of files with symbolic links.

Write a POSIX-compatible shell script `practice_q8.sh`, which takes 0 or more names of files as arguments, and prints commands to replace some of the files with symbolic links.

We need to check the commands before executing them, so `practice_q8.sh` should print the commands, *not* execute them.

For each file specified as an argument, if the file has identical contents (bytes) to any previous file specified as an argument, `practice_q8.sh` should print a [ln](https://manpages.debian.org/jump?q=ln.1) command which would replace the file with a symbolic link to the previous file.

`practice_q8.sh` should just print the [ln](https://manpages.debian.org/jump?q=ln.1) command, it should *not* execute the [ln](https://manpages.debian.org/jump?q=ln.1) command.

If none of the files can be replaced by symbolic links, `practice_q8.sh` should print a message exactly as shown in the last example below.

Your script must work when executed with `/bin/dash` on a CSE system, and must only use the external programs listed below.

Make your program produce **exactly** the output indicated by the example below.

For example, here is how your program should behave:

```
./practice_q8.sh file0.txt file1.txt file2.txt file3.txt file4.txt file5.txt file6.txt file7.txt file8.txt
ln -s file0.txt file3.txt
ln -s file1.txt file6.txt
ln -s file2.txt file5.txt
ln -s file2.txt file7.txt
./practice_q8.sh file6.txt file4.txt file1.txt file2.txt file3.txt file5.txt file7.txt file8.txt file0.txt
ln -s file6.txt file1.txt
ln -s file2.txt file5.txt
ln -s file2.txt file7.txt
ln -s file3.txt file0.txt
./practice_q8.sh file8.txt file7.txt file6.txt file5.txt file4.txt file3.txt file2.txt file1.txt file0.txt
ln -s file7.txt file5.txt
ln -s file7.txt file2.txt
ln -s file6.txt file1.txt
ln -s file3.txt file0.txt
./practice_q8.sh file1.txt file2.txt file3.txt file4.txt file5.txt file6.txt
ln -s file1.txt file6.txt
ln -s file2.txt file5.txt
./practice_q8.sh file0.txt file1.txt file2.txt file3.txt file4.txt
ln -s file0.txt file3.txt
./practice_q8.sh file3.txt file0.txt
ln -s file3.txt file0.txt
./practice_q8.sh file3.txt file0.txt file3.txt file0.txt file3.txt file0.txt file3.txt file0.txt
ln -s file3.txt file0.txt
./practice_q8.sh file1.txt file2.txt file3.txt file4.txt
No files can be replaced by symbolic links
```

- Your program should **not** change any files or create any links; it should just print commands to do so.
- Your program can assume any supplied arguments are the names of ordinary files.
- Your program can assume filenames do not contain whitespace, and do not contain slashes.
- Your program can **not** assume anything about the contents of the files. The files may contain any number of any character and any number of lines.
- You are permitted to use these and only these external programs:
  - [basename](https://manpages.debian.org/jump?q=basename.1)
  - [cat](https://manpages.debian.org/jump?q=cat.1)
  - [chmod](https://manpages.debian.org/jump?q=chmod.1)
  - [cmp](https://manpages.debian.org/jump?q=cmp.1)
  - [cp](https://manpages.debian.org/jump?q=cp.1)
  - [cut](https://manpages.debian.org/jump?q=cut.1)
  - [diff](https://manpages.debian.org/jump?q=diff.1)
  - [dirname](https://manpages.debian.org/jump?q=dirname.1)
  - [echo](https://manpages.debian.org/jump?q=echo.1)
  - [expr](https://manpages.debian.org/jump?q=expr.1)
  - [false](https://manpages.debian.org/jump?q=false.1)
  - [find](https://manpages.debian.org/jump?q=find.1)
  - [grep](https://manpages.debian.org/jump?q=grep.1)
  - [head](https://manpages.debian.org/jump?q=head.1)
  - [ls](https://manpages.debian.org/jump?q=ls.1)
  - [mkdir](https://manpages.debian.org/jump?q=mkdir.1)
  - [mv](https://manpages.debian.org/jump?q=mv.1)
  - [printf](https://manpages.debian.org/jump?q=printf.1)
  - [pwd](https://manpages.debian.org/jump?q=pwd.1)
  - [rev](https://manpages.debian.org/jump?q=rev.1)
  - [rm](https://manpages.debian.org/jump?q=rm.1)
  - [rmdir](https://manpages.debian.org/jump?q=rmdir.1)
  - [sed](https://manpages.debian.org/jump?q=sed.1)
  - [seq](https://manpages.debian.org/jump?q=seq.1)
  - [sort](https://manpages.debian.org/jump?q=sort.1)
  - [stat](https://manpages.debian.org/jump?q=stat.1)
  - [strings](https://manpages.debian.org/jump?q=strings.1)
  - [tac](https://manpages.debian.org/jump?q=tac.1)
  - [tail](https://manpages.debian.org/jump?q=tail.1)
  - [tee](https://manpages.debian.org/jump?q=tee.1)
  - [test](https://manpages.debian.org/jump?q=test.1)
  - [touch](https://manpages.debian.org/jump?q=touch.1)
  - [tr](https://manpages.debian.org/jump?q=tr.1)
  - [true](https://manpages.debian.org/jump?q=true.1)
  - [uniq](https://manpages.debian.org/jump?q=uniq.1)
  - [wc](https://manpages.debian.org/jump?q=wc.1)
  - [xargs](https://manpages.debian.org/jump?q=xargs.1)
- You are permitted to use any built-in shell features including:
  - `case`
  - `cd`
  - `exit`
  - `for`
  - `if`
  - `read`
  - `shift`
  - `while`
- You may not use non-POSIX-compatible Shell.
  You are not permitted to use `/bin/bash` or `/bin/sh`.
  You can assume anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.
- You may not use Perl, C, Python, awk, or any other language.
- You **may not** create temporary files.
- No error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q8
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q8 practice_q8.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q8.sh`

```
#!/bin/dash

for file1 in "$@"; do
    processed="$processed $file1 "
    for file2 in "$@"; do
        case "$processed" in
            *" $file2 "*)
                continue
                ;;
        esac

        diff "$file1" "$file2" > /dev/null || continue

        echo ln -s "$file1" "$file2"
        processed="$processed $file2 "
        printed=1

    done
done

test -z "$printed" && echo No files can be replaced by symbolic links
```

### Question 9 (8 marks)



Write a Python program, `practice_q9.py`, which takes two command line argument, a positive integer **n** and the name of a file.

the single positive integer, **n**, indicating a maximum desired line length.

Your program should change the file in the following way:

- Lines containing **n** characters or less, not including the new line, should not be changed.
- Lines not containing a space character (' ') should not be changed.
- Lines containing more than **n** characters with a space in the first **n** characters,
  should have the last space in the first **n** characters changed to a newline character ('\n').
- Lines containing more than **n** characters without a space in the first **n** characters,
  should have the first space on the line changed to a newline character ('\n').

The above rules should also be applied to new lines as they are created.

Your program should not print anything to stdout.
The only thing it should do is change the file in-place.

For example:

```
echo hello there how are you today > hello.txt
./practice_q9.py 80 hello.txt
cat hello.txt
hello there how are you today
./practice_q9.py 23 hello.txt
cat hello.txt
hello there how are
you today
./practice_q9.py 12 hello.txt
cat hello.txt
hello there
how are you
today
./practice_q9.py 6 hello.txt
cat hello.txt
hello
there
how
are
you
today
cp frost.txt f.txt
cat f.txt 
I shall be telling this with a sigh
Somewhere ages and ages hence:
Two roads diverged in a wood, and I --
I took the one less traveled by,
And that has made all the difference.
./practice_q9.py 20 f.txt
cat f.txt 
I shall be telling
this with a sigh
Somewhere ages and
ages hence:
Two roads diverged
in a wood, and I --
I took the one less
traveled by,
And that has made
all the difference.
./practice_q9.py 10 f.txt
cat f.txt 
I shall
be telling
this with
a sigh
Somewhere
ages and
ages
hence:
Two roads
diverged
in a
wood, and
I --
I took
the one
less
traveled
by,
And that
has made
all the
difference.
```

Note `practice_q9.py` printed nothing - it changed the file it was given as argument.

Make sure your program does this.

- Your program can assume it is given one argument which is the name of a file.
- Your program can assume the file exists.
- You can assume the files contains only ASCII bytes.
- You can assume the file is small enough to fit in memory, e.g. the lines can be read into a list.
- Your program should print nothing to stdout.
- You **are** permitted to create temporary files.
- Your answer **must** be `Python` only.
- You **may** `use` any standard `Python` modules.
  Unless they are otherwise disallowed by the following restrictions.
- You **may not** use `Shell`, `C`, `Perl`, or any other language.
- You **may not** run external programs, e.g. via the `subprocess` module, or any other method.
- You **may not** import, or otherwise use, the `textwrap` module.
- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q9
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q9 practice_q9.py
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q9.py`

```
#!/usr/bin/python3

import fileinput, sys

def fmt(n, line):
    if len(line) <= n:
        return line
    space_indexes = [i for i, c in enumerate(line) if c == " "]
    if not space_indexes:
        return line
    index = space_indexes[0]
    space_indexes_less_n = [i for i in space_indexes if i < n]
    if space_indexes_less_n:
        index = space_indexes_less_n[-1]
    return line[:index] + "\n" + fmt(n, line[index + 1:])


n = int(sys.argv[1])
with fileinput.input(files=sys.argv[2], inplace=True) as f:
    for line in f:
        print(fmt(n, line.rstrip("\n")))
```

### Question 10 (8 marks)



Write a Python program, `practice_q10.py`, that reads lines of text from its standard input and prints them to its standard output with the words which are not ***balanced\*** removed.

A word is ***balanced\*** if every character in the word occurs exactly n times (for some value of n).

Case should be ignored when considering whether a word is balanced.

For example: **Gaga** is balanced because '**g**' occurs twice and '**a**' occurs twice.

For example: **gauge** is not balanced because '**g**' occurs twice but '**u**', '**a**', and '**e**' occur once.

Assume that a word is any sequence of non-whitespace characters.
For example, **tock-tock** is considered a single word.

You should print the words separated by a single space character.

Match the example output below **exactly**. For example:

```
cat frost.txt
I shall be telling this with a sigh
Somewhere ages and ages hence:
Two roads diverged in a wood, and I --
I took the one less traveled by,
And that has made all the difference.
./practice_q10.py < frost.txt
I be this with a sigh
ages and ages
Two roads in a and I --
I the one by,
And has made the
cat interesting_words.txt
1 duck   bulbul  Gaga    tocktocktock  wwwwweeeee
2 goose baboon bonobo   Guage tock-tock  wwwwweee
3 xerophytic   Deeded sestettes     zZz teammate horseshoer happenchance
4   elephant decorator    agaga  teammates            horseshoe
./practice_q10.py <  interesting_words.txt
1 duck bulbul Gaga tocktocktock wwwwweeeee
2
3 xerophytic Deeded sestettes zZz teammate horseshoer happenchance
4
./practice_q10.py < story.txt | head
THE LEAP-FROG

A Flea, a and a Leap-frog once wanted to
could jump and they the whole world,
and who chose to come to the
festival. famous jumpers they, as
would say, when they met in the

"I give my daughter to him who jumps
the King; "for it is not so amusing
./practice_q10.py < story.txt | tail
The Flea then went into foreign it is said,
he was

The sat on a bank, and
on things; and he said "Yes, a fine
is fine is what care
about." And then he began his peculiar
song, from we have taken this history; and may,
very be it does stand
printed in black and white.
```

- Your program may read all lines before producing any output.
- Your program may produce output one line at a time.
- Your program can assume its input contains only ASCII bytes.
- Your answer **must** be `Python` only.
- You **may** `use` any standard `Python` modules.
  Unless they are otherwise disallowed by the following restrictions.
- You **may not** use `Shell`, `C`, `Perl`, or any other language.
- You **may not** run external programs, e.g. via the `subprocess` module, or any other method.
- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q10
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q10 practice_q10.py
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q10.py`

```
#!/usr/bin/python3

import sys

def is_equi_word(word):
    letter_count = {}
    for letter in word.lower():
        letter_count[letter] = letter_count.get(letter, 0) + 1
    return len(set(letter_count.values())) == 1

for line in sys.stdin:
    words = line.split()
    equi_words = filter(is_equi_word, words)
    print(' '.join(equi_words))
```

### Question 11 (8 marks)



We need a program to check if the same files are present in two directory trees.

Write a POSIX-compatible Shell script, `practice_q11.sh`, which is given either 2 arguments which are the pathnames of directories.

`practice_q11.sh` should print a single line of output containing 4 integers:



- number of files that are present at the same position in both directory trees and are the same size.
- number of files that are present at the same position in both directory trees but are different sizes.
- number of files that are present only in the first directory tree.
- number of files that are present only in the second directory tree.

Note, a file needs to be present in both directory trees at the same relative pathname to be counted.

For example, if we are comparing the directory trees **dir1** and **dir2**. and the file **dir1/2041/lab09/answer.py** exists in the first directory tree,

We consider it present in the second directory tree only if the file **dir2/2041/lab09/answer.py** exists.

Other files named **answer.py** elsewhere in the second directory tree, e.g. **dir2/2521/lab05/answer.py** are not counted.

When a file is present at the same relative pathname in both directory trees `practice_q11.sh` does not have to check if it contains the same contents (bytes), just whether both files are the same size (same number of bytes).

For example:
these commands create 2 directory trees named **d1** and **d2** containing 3 files of the same name.

```
mkdir -p d1/b/c
echo hello andrew > d1/file1
echo bye andrew > d1/b/file2
echo 1 > d1/b/c/one
mkdir -p d2/b/c
echo HELLO andrew > d2/file1
echo Bye Andrew > d2/b/file2
echo 2 > d2/b/c/one
```

The contents of the 3 files are different but their sizes are the same.
**practice_q11.sh** reports 3 files present in both tree of the same size:

```
./practice_q11.sh d1 d2
3 0 0 0
```

If we change the size of `file1` in the first directory tree **practice_q11.sh** reports 2 files present in both trees of the same size. and 1 file present in both trees but of a different size:

```
echo hello everyone >d1/file1
./practice_q11.sh d1 d2
2 1 0 0
```

If we add a file to the second directory tree:

```
echo 3 > d2/b/c/three
./practice_q11.sh d1 d2
2 1 0 1
```

If we add a different file to the first directory tree:

```
echo 3 > d1/b/three
./practice_q11.sh d1 d2
2 1 1 1
```

Note, the first directory tree contains a file named **b/three** and the second tree contains a file named **b/c/three**.
This is not considered as the file being present in both directory trees, as the relative pathname of each file is different.

Autotest will only be of limited assistance in debugging your program.
Do not expect autotest messages to be easy to understand for this problem.
You will need to debug your program yourself.

- You do not need to examine the bytes of files, just the files size (number of bytes in the file).
  You can however assume files contain only ASCII bytes and are small enough to read their bytes.

- Your program does **not** have to consider permissions, modification times, or other file metadata.

- You **can** assume the directory trees to be compared contain only directories and regular files.
  You **can** assume they do not contain links or other special files.
  You **can** assume they do not contain sparse files.

- You are **only** permitted to use these external programs:

  - `basename`
  - `cat`
  - `chmod`
  - `cmp`
  - `cp`
  - `cut`
  - `diff`
  - `dirname`
  - `echo`
  - `expr`
  - `false`
  - `find`
  - `grep`
  - `head`
  - `ls`
  - `mkdir`
  - `mktemp`
  - `mv`
  - `printf`
  - `pwd`
  - `rev`
  - `rm`
  - `rmdir`
  - `sed`
  - `seq`
  - `sort`
  - `stat`
  - `strings`
  - `tac`
  - `tail`
  - `tee`
  - `test`
  - `touch`
  - `tr`
  - `true`
  - `uniq`
  - `wc`
  - `xargs`

  See `man 1 <program>` for more info on any program

- You are permitted to use **any** built-in shell features including:

  - `case`
  - `cd`
  - `exit`
  - `for`
  - `if`
  - `read`
  - `shift`
  - `while`

  See `man 1 dash` for more info on any built-in

  See `help <built-in>` for *bash* info on any built-in (might not be POSIX-compatible)

- You **may not** use non-POSIX-compatible shell features.
  You **are not permitted** to use `/bin/bash`, `/bin/sh`, or any other shell.
  Make the first line of your shell-script `#!/bin/dash`
  You **can** assume that anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.

- You **may not** use `Perl`, `C`, `Python`, `awk` or any language other than shell.

- You **may** create temporary files.

- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q11
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q11 practice_q11.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q11.sh`

```
#!/bin/dash
unset CDPATH

for d in "$1" "$2"; do
    (cd "$d" || exit 1; find . -type f)
done |
sort |
uniq | (
    same_size=0
    different_size=0
    tree1_only=0
    tree2_only=0
    while read pathname
    do
        if test ! -f "$2/$pathname"
        then
            tree1_only=$((tree1_only + 1))
        elif test ! -f "$1/$pathname"
        then
            tree2_only=$((tree2_only + 1))
        elif test "$(stat -c '%s' "$1/$pathname")" != "$(stat -c '%s' "$2/$pathname")"
        then
            different_size=$((different_size + 1))
        else
            same_size=$((same_size + 1))
        fi
    done
    echo $same_size $different_size $tree1_only $tree2_only
)
```

### Question 12 (8 marks)

Write a POSIX-compatible Shell script practice_q12.sh which given a square on the chessboard. prints in successive lines the squares that can be reached by a knight.

A chessboard is an 8x8 square matrix. We label each square as below:



```
a8 b8 c8 d8 e8 f8 g8 h8
a7 b7 c7 d7 e7 f7 g7 h7
a6 b6 c6 d6 e6 f6 g6 h6
a5 b5 c5 d5 e5 f5 g5 h5
a4 b4 c4 d4 e4 f4 g4 h4
a3 b3 c3 d3 e3 f3 g3 h3
a2 b2 c2 d2 e2 f2 g2 h2
a1 b1 c1 d1 e1 f1 g1 h1
```

A knight makes an L-shaped move. It moves either two squares horizontally and one square vertically or two squares vertically and one square horizontally.

For example, a knight at *d4* can move to one of eight squares: *c2*, *e2*, *b3*, *b5*, *c6*, *e6*, *f3* or *f5*.

A move can not take a knight off the chessboard. Hence, a knight on square near the edge of the board will have fewer possible moves.

For example, a knight at *a1* can move only to *c2* and *b3*.

Your program should take one argument: a starting square.

It should print a sequence of lines.

The first line should contain only the starting square

The second line should contain squares a knight can move to from the starting square.

The third line should contain **new** squares a knight can move to from squares listed on the second line.

The fourth line should contain **new** squares a knight can move to from squares listed on the third line.

You program should stop when no **new** squares can be reached.

The squares on each line should be printed in sorted order, separated by a single space.

Match the output format below EXACTLY.

For example:



```
./practice_q12.sh a1
a1
b3 c2
a3 a5 b4 c1 c5 d2 d4 e1 e3
a2 a4 a6 b1 b5 b7 c4 c6 d1 d3 d5 d7 e2 e4 e6 f1 f3 f5 g2 g4
a7 b2 b6 b8 c3 c7 d6 d8 e5 e7 f2 f4 f6 f8 g1 g3 g5 g7 h2 h4 h6
a8 c8 e8 f7 g6 g8 h1 h3 h5 h7
h8
./practice_q12.sh d4
d4
b3 b5 c2 c6 e2 e6 f3 f5
a1 a3 a5 a7 b4 b8 c1 c3 c5 c7 d2 d6 d8 e1 e3 e5 e7 f4 f8 g1 g3 g5 g7 h2 h4 h6
a2 a4 a6 a8 b1 b7 c4 c8 d1 d3 d5 d7 e4 e8 f1 f7 g2 g4 g6 g8 h1 h3 h5 h7
b2 b6 f2 f6 h8
./practice_q12.sh g2
g2
e1 e3 f4 h4
c2 c4 d1 d3 d5 e2 e6 f1 f3 f5 g4 g6 h3 h5
a1 a3 a5 b2 b4 b6 c1 c3 c5 c7 d2 d4 d6 d8 e5 e7 f2 f6 f8 g1 g3 g5 g7 h2 h6 h8
a2 a4 a6 a8 b1 b3 b5 b7 c6 c8 d7 e4 e8 f7 g8 h1 h7
a7 b8
```

- Your program must complete in 60 seconds.

- Your can assume there is one command-line argument and it is valid square.

- No error checking is necessary.

- You **are** permitted to create temporary files.

- You are **only** permitted to use these external programs:

  - `basename`
  - `cat`
  - `chmod`
  - `cmp`
  - `cp`
  - `cut`
  - `diff`
  - `dirname`
  - `echo`
  - `expr`
  - `false`
  - `find`
  - `grep`
  - `head`
  - `ls`
  - `mkdir`
  - `mktemp`
  - `mv`
  - `printf`
  - `pwd`
  - `rev`
  - `rm`
  - `rmdir`
  - `sed`
  - `seq`
  - `sort`
  - `stat`
  - `strings`
  - `tac`
  - `tail`
  - `tee`
  - `test`
  - `touch`
  - `tr`
  - `true`
  - `uniq`
  - `wc`
  - `xargs`

  See `man 1 <program>` for more info on any program

- You are permitted to use **any** built-in shell features including:

  - `case`
  - `cd`
  - `exit`
  - `for`
  - `if`
  - `read`
  - `shift`
  - `while`

  See `man 1 dash` for more info on any built-in

  See `help <built-in>` for *bash* info on any built-in (might not be POSIX-compatible)

- You **may not** use non-POSIX-compatible shell features.
  You **are not permitted** to use `/bin/bash`, `/bin/sh`, or any other shell.
  Make the first line of your shell-script `#!/bin/dash`
  You **can** assume that anything that works with the version of `/bin/dash` on CSE systems is POSIX compatible.

- You **may not** use `Perl`, `C`, `Python`, `awk` or any language other than shell.

- **No** error checking is necessary.

When you think your program is working, you can run some simple automated tests:

```
2041 autotest practice_q12
```

When you are finished working on this activity, you must submit your work by running give:

```
give cs2041 practice_q12 practice_q12.sh
```

To verify your submissions for this activity:

```
2041 classrun -check
```

Sample solution for `practice_q12.sh`

```
#!/bin/dash

squares="$1"
squares_regex=XX

while test -n "$squares"
do
    echo "$squares"
    squares_regex="$squares_regex|$(echo "$squares"| tr ' ' '|')"
    squares="$(
        for square in $squares
        do
            column_number="$(echo "$square"|cut -c1|tr abcdefgh 12345678)"
            row_number="$(echo "$square"|cut -c2)"
            for column_delta in -2 -1 1 2
            do
                for row_delta in -2 -1 1 2
                do
                    test "$(echo $row_delta|tr -d -)" = "$(echo $column_delta|tr -d -)" &&
                        continue
                    new_row=$((row_number + row_delta))
                    new_column_number=$((column_number + column_delta))
                    new_column=$(echo $new_column_number|tr 12345678 abcdefgh)
                    echo "$new_column$new_row"
                done
            done
        done|
        sort|
        uniq|
        grep '^[a-h][1-8]$'|
        grep -Ev "$squares_regex"|
        tr '\n' ' '|
        sed 's/ *$//'
    )"
done
```