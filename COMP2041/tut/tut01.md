<center><font size=6pt>Week 01 Tutorial Questions (Objectives)</font></center>

1. What is an operating system?

   > An operating system is a piece of software that manages the hardware of a computer and provides an interface to the programs that run on the computer.
   >
   > This means that user level programs do not need to know the details of the hardware.
   > They use code that interfaces with the operating system (syscalls).
   > And the operating system handles the details of the hardware.
   >
   > This means that user level programs can be written once and run on many different computers.

2. What operating systems are being used in your house/tutorial room?

   > Operating systems in your room might include:
   >
   > - (Linux) Ubuntu, Debian, Arch, Gentoo, Red Hat, Fedora, Android, SteamOS (Arch derivative), [etc](https://en.wikipedia.org/wiki/List_of_Linux_distributions), [etc](https://upload.wikimedia.org/wikipedia/commons/1/1b/Linux_Distribution_Timeline.svg).
   > - (Darwin (Apple)) macOS (previously: OS X (previously: mac OS X)), iOS, iPadOS, WatchOS, [etc](https://en.wikipedia.org/wiki/List_of_Apple_operating_systems), [etc](https://photos2.insidercdn.com/osxserver101409-1.png).
   > - (Windows (Microsoft)) Windows, Windows Phone, Windows Mobile, Xbox, [etc](https://en.wikipedia.org/wiki/List_of_Microsoft_operating_systems), [etc](https://upload.wikimedia.org/wikipedia/commons/3/39/Microsoft_timeline_of_operating_systems_2.png).
   > - (BSD) FreeBSD, NetBSD, OpenBSD, PlaystationOS (FreeBSD derivative) [etc](https://en.wikipedia.org/wiki/List_of_BSD_operating_systems).
   >
   > [Family Tree](https://eylenburg.github.io/pics/Eylenburg_Operating_System_Timeline_Family_Tree.svg).

3. What operating system(s) do CSE lab computers run?

   > CSE's lab computers and servers run (Linux) Debian (currently version 5.10).
   >
   > This web server is currently running:
   >
   > ```shell
   > uname -a
   > Linux dvorak 4.19.0-23-amd64 #1 SMP Debian 4.19.269-1 (2022-12-20) x86_64 GNU/Linux
   > ```

4. Write a regex to match:

   1. C preprocessor commands in a C program source file.

      > 1. Given this definition:
      >
      >    In C code any (and only) lines that immediately start with `#` are preprocessor commands.
      >
      >    This regex will match the majority of preprocessor commands.
      >
      >    ```
      >    ^#
      >    ```
      >
      >    `^` is an **anchor** that matches the start of a line.
      >    `#` matches the character `#`.
      >
      >    Thus `^#` matches a line that starts with `#`.
      >
      >    But given the following definition from the [GCC documentation](https://gcc.gnu.org/onlinedocs/cpp/The-preprocessing-language.html):
      >
      >    Preprocessing directives are lines in your program that start with ‘#’. Whitespace is allowed before and after the ‘#’. The ‘#’ is followed by an identifier
      >
      >    A better regex would be:
      >
      >    ```
      >    ^\s*#\s*[_A-Za-z]
      >    ```
      >
      >    `\s` is a **Special Expression** that matches any white space character.
      >    It is a shorthand for `[[:space:]]`
      >    which itself is equivalent to `[ \t\r\n\f]`
      >    this is: space, tab, carriage return, newline or form feed.
      >
      >    `*` is the repetition quantifier that matches the previous pattern zero or more times.
      >
      >    So `\s*` matches zero or more white space characters.
      >
      >    `[_A-Za-z]` is a **bracket expression**
      >    `A-Z` is a **range expression** that represents all the characters between `A` and `Z` inclusive.
      >    `a-z` is a **range expression** that represents all the characters between `a` and `z` inclusive.
      >
      >    Thus `[_A-Za-z]` matches any uppercase or lowercase letter plus underscore.
      >
      >    These are the only characters that are allowed to start a C identifier.

   2. All the lines in a C program except preprocessor commands.

      > 1. If we use the first definition of a preprocessor command:
      >
      >    ```
      >    ^#
      >    ```
      >
      >    Then we can match all the lines in a C program except preprocessor commands with:
      >
      >    ```
      >    ^[^#]|^$
      >    ```
      >
      >    `^` is an **anchor** that matches the start of a line.
      >    `[^#]` matches any character that is not `#`.
      >    `|` is an **alternation** that matches either the left or right side.
      >    `$` is an **anchor** that matches the end of a line.
      >
      >    Thus `^[^#]` matches a line that starts with any character that is not `#`.
      >
      >    `[^#]` is a **bracket expression**.
      >    A bracket expression matches any character that is given in the class.
      >    eg: `[abc]` matches `a` or `b` or `c`.
      >    If the first character in a bracket expression is `^` then the class matches any character that is not given in the class.
      >    So `[#]` matches `#` and `[^#]` matches any character that is not `#`.
      >
      >    Note that bracket expressions only match a single character.
      >    so `[abc]` matches one character that is either `a` or `b` or `c`.
      >    not `a` followed by `b` followed by `c`.
      >    that would be `abc`.
      >    But this means that `[^abc]` doesn't match anything other than `abc`
      >    It means that `[^abc]` matches a single character that is not `a` or `b` or `c`.
      >
      >    `[^#]` must match a single character that is not `#`.
      >    but it **must match** so `^[^#]` by itself will not match an empty line.
      >    The second part of the pattern `^$` only matches an empty line.
      >
      >    But using the second definition of a preprocessor command:
      >
      >    ```
      >    ^\s*#\s*[_A-Za-z]
      >    ```
      >
      >    It is a little more complicated.
      >    In fact it is impossible to do this with a normal Extended Regular Expression.
      >    You need to use a Perl Compatible Regular Expression.
      >
      >    ```
      >    ^(?! *#).*$
      >    ```
      >
      >    `(?!...)` is a **negative look ahead**.
      >    It is like using `[^...]` but for strings instead of characters (and it doesn't consume any characters).

   3. All lines in a C program with trailing white space (one or more white space at the end of line).

      > ```
      > \s$
      > ```
      >
      > `\s` is a **bracket expression** that matches any white space character.
      > `$` is an **anchor** that matches the end of a line.
      >
      > Thus `\s$` matches a line that ends with a white space character.
      >
      > `\s` is a shorthand for the pre-defined bracket expression `[ \t\r\n\f]`
      > That is it matches a space, a tab, a carriage return, a newline or a form feed.
      > ie any white space character.
      > This can also be written as `[[:space:]]`
      > `[:space:]` is a **character class**
      > This is also a shorthand for `[ \t\r\n\f]` (in English).
      > The contents of a character class are locale dependent.

   4. The names "Barry", "Harry", "Larry" and "Parry".

      > ```
      > [BHLP]arry
      > ```
      >
      > `[BHLP]` is a **bracket expression** that matches any character that is `B` or `H` or `L` or `P`.
      > `arry` matches the characters `a` followed by `r` followed by `r` followed by `y`.

   5. A string containing the word "hello" followed, some time later, by the word "world".

      > ```
      > hello.*world
      > ```
      >
      > `hello` matches the literal string "hello".
      > `.*` matches any character zero or more times.
      > `world` matches the literal string "world".
      >
      > `.*` is perhaps the most common regex pattern.
      > `.` is a **wildcard**, it matches any single character. With the single exception of newline.
      > `*` is the **optional repetition** **quantifier**, it matches the previous pattern zero or more times.
      > together `.*` matches any characters zero or more times.
      > This effectively says "i don't care what is in between the other parts of the pattern".
      >
      > `*` is a **greedy** quantifier, it will match as many characters as possible.
      > so in the pattern `hello.*world` it will match the longest string that starts with `hello` and ends with `world`.
      > eg. `helloworld` or `hello, cruel world` or `hello, world, hello, world`
      > In call cases the last `world` is matched, ie it doesn't stop at the first `world`.

   6. The word "calendar" and mis-spellings where 'a' is replaced with 'e' or vice-versa.

      > ```
      > c[ae]l[ae]nd[ae]r
      > ```
      >
      > `c` matches the literal character `c`.
      > `[ae]` is a **bracket expression** that matches any character that is `a` or `e`.
      > `l` matches the literal character `l`.
      > `[ae]` is a **bracket expression** that matches any character that is `a` or `e`.
      > `nd` matches the literal string `nd`.
      > `[ae]` is a **bracket expression** that matches any character that is `a` or `e`.
      > `r` matches the literal character `r`.
      >
      > So this matches the literal strings `calandar`, `calander`, `calendar`, `calender`, `celandar`, `celander`, `celendar`, `celender`.

   7. A list of positive integers separated by commas, e.g. `2,4,8,16,32`

      > ```
      > ([1-9][0-9]*|0)(,([1-9][0-9]*|0))*
      > ```
      >
      > `[1-9]` is a **bracket expression** that matches any character that is `1` or `2` or `3` or `4` or `5` or `6` or `7` or `8` or `9`.
      > `[0-9]` is a **bracket expression** that matches any character that is `0` or `1` or `2` or `3` or `4` or `5` or `6` or `7` or `8` or `9`.
      > `*` is the **optional repetition** **quantifier**, it matches the previous pattern zero or more times.
      > `,` matches the literal character `,`.
      > `[1-9][0-9]*` matches a string of digits that starts with a non-zero digit.
      > `|0` also matches the literal character `0`. as this isn't allowed in the first part of the pattern.
      > `(,([1-9][0-9]*|0))*` matches zero or more strings of digits that start with a non-zero digit and are separated by a comma.

   8. A C string whose last character is newline.

      > ```
      > "[^"]*\\n"
      > ```
      >
      > Note: this doesn't handle escaped quotes.
      > regex *cannot handle* escaped quotes.
      >
      > `"` matches the literal character `"`.
      > `[^"]` is a **bracket expression** that matches any character that is not `"`.
      > `*` is the **optional repetition** **quantifier**, it matches the previous pattern zero or more times.
      > `\\` matches the literal character `\`.
      > `n` matches the literal character `n`.
      > `"` matches the literal character `"`.
      >
      > `[^X]*` is also a very common regex pattern.
      > `[^X]*` solves the problem created by `.*` of matching too much.
      > As `.*` is **greedy** it will match as much as possible.
      > in a situation where you want to match everything between two parts of a string `.*` often matches too much.
      > The solution is to use `[^X]*` instead of `.*`, where `X` is the character that ends the string.

5. When should you use:

   - `fgrep`/`grep -F`
   - `grep`/`grep -G`
   - `egrep`/`grep -E`
   - `pgrep`/`grep -P`

   > - `fgrep` and the same command `grep -F`.
   >   `fgrep` is the old command and is [deprecated](https://en.wikipedia.org/wiki/Deprecation#Software).
   >   `grep -F` should be used instead.
   >
   >   `grep -F` just does string matching - not regular expression matching.
   >   -F stands for Fixed String.
   >
   >   In fixed strings no characters have a special meaning.
   >   Each character matches exactly itself.
   >
   >   Fixed string matching is faster than regular expression matching.
   >
   >   Use `grep -F` when you don't need the power regular expressions.
   >   Eg. When you want to find a literal word in a file
   >   Eg. When you need to find characters in a file that would otherwise have special meaning.
   >
   > - `grep` and the same command `grep -G`.
   >   -G exists to reset `grep` to it's default mode after it has been changed.
   >   Eg. `grep -F -G`.
   >
   >   `grep` implements basic regular expressions BRE.
   >
   >   It does so for historic reasons to do with the available processing power on old computers.
   >   Most of the time you don't want to use `grep`.
   >   You probably want to use `grep -E` as your goto command.
   >
   > - `egrep` and the same command `grep -E`.
   >   `egrep` is the old command and is [deprecated](https://en.wikipedia.org/wiki/Deprecation#Software).
   >   `grep -E` should be used instead.
   >
   >   `grep -E` implements extended regular expressions ERE.
   >
   >   You probably want to use `grep -E` when you need regular expressions.
   >
   > - `pgrep` isn't related to the other commands in the `grep` family.
   >   [pgrep](https://manpages.debian.org/jump?q=pgrep.1) - look up processes based on name and other attributes.
   >
   >   `grep -P` implements perl compatible regular expressions PCRE.
   >
   >   `grep -P` is rarely needed/used to do clever/complicated things that BRE and ERE cannot do.

6. grep takes many options (see the manual page for [grep](https://manpages.debian.org/jump?q=grep.1)).

   ```shell
   man 1 grep
   ```

   Give 3 (or more) simple/important options grep takes and explain what they do.

   > - For:
   >
   >   - `-F, --fixed-strings`
   >
   >   - `-G, --basic-regexp`
   >
   >   - `-E, --extended-regexp`
   >
   >   - `-P, --perl-regexp`
   >
   > See the previous question.
   >
   > - `-i, --ignore-case` ignores differences in (upper/lower) case when matching characters.
   >
   >   Very useful as you often want this behaviour.
   >
   > - `-v, --invert-match` non-matching lines are printed.
   >
   >   Very useful because it is often easier to define a regex for lines you don't want.
   >
   > - `-c, --count` prints the number of lines containing a match.
   >
   >   Very useful for finding how common a pattern is.
   >
   > - `-w, --word-regexp` prints lines where the regex matches a whole word.
   >
   >   Very useful for example for matching variables names in code.
   >
   >   This is the same as adding `\b` to the start and end of your regex.
   >
   > - `-x, --line-regexp` prints lines where the regex matches the whole line.
   >
   >   Very useful as it is common to write an regexp to exactly match the entire line.
   >
   >   This is the same as adding `^` and `$` to the start and end of your regex respectively.
   >
   > - Other useful options: -o/-s/-q, -A/-B/-C, -H/-n/-b

7. Why does this command seem to be taking a long time to run:

   ```shell
   grep -E hello
   ```

   > `grep -E` is reading from stdin, printing strings that contain **hello**
   >
   > `grep -E`, if it is not given any filenames as arguments, reads from stdin.

8. Why won't this command work:

   ```shell
   grep -E int main program.c
   ```

   > `grep -E` will attempt to search files **main** and **program.c** for lines containing the string **int**
   >
   > This is because space has a special meaning to the shell - it separates arguments.
   >
   > This will do what is likely intended - search **program.c** for lines containing the string **int main**
   >
   > ```shell
   > grep -E 'int main' program.c
   > ```

9. Give five reasons why this attempt to search a file for HTML paragraph and break tags may fail.

   ```shell
   grep <p>|<br> /tmp/index.html
   ```

   Give a `grep` command that will work.

   > The characters '<', '>' and '|' are part of the shell's syntax (meta characters) and the shell will interpret them rather than passing them to grep. This can be avoided with singleor double-quotes or backslash, e.g:
   >
   > ```shell
   > egrep '<p>|<br>' /tmp/index.html
   > egrep "<p>|<br>" /tmp/index.html
   > egrep \<p>\|<br\> /tmp/index.html
   > ```
   >
   > For historical reasons `grep` doesn't implement alternation ('|'). You need to use `grep -E` instead to get the full power of regular expressions.
   >
   > The supplied regular expression won't match the HTML tags if they are in upper case (A-Z), e.g: `<P>`. The match can be case insensitive by changing the regular expression or using grep's -i flag
   >
   > ```shell
   > grep -E '<[pP]>|<[bB][rR]>' /tmp/index.html
   > grep -Ei '<p>|<br>' /tmp/index.html
   > ```
   >
   > The supplied regular expression also won't match HTML tags containing spaces, e.g: `<p >`. This can be remedied by changing the regular expression
   >
   > ```shell
   > grep -Ei '< *(p|br) *>' /tmp/index.html
   > ```
   >
   > The HTML tag may contain attributes, e.g: `<p class="lead_para">`. Again can be remedied by changing the regular expression or using egrep's -w flag.
   >
   > ```shell
   > grep -Ei '< *(p|br)[^>]*>' /tmp/index.html
   > ```
   >
   > This will still match `<pre>`. This can be avoided using a more complex regex:
   >
   > ```shell
   > grep -Ei '< *(p|br)( [^>]*)*>' /tmp/index.html
   > ```
   >
   > The HTML tag might contain a newline. This is more difficult to handle with a line-based tool like `grep`.

10. For each of the regular expression below indicate how many different strings the pattern matches and give some example of the strings it matches.
    If possible these example should include the shortest string and the longest string.

    1. ```
       Perl
       ```

    2. ```
       Pe*r*l
       ```

    3. ```
       Full-stop.
       ```

    4. ```
       [1-9][0-9][0-9][0-9]
       ```

    5. ```
       I (love|hate) programming in (Perl|Python) and (Java|C)
       ```
       
       > | Regexp                                                     | N Matches                                     | Shortest Match                     | Longest Match                           | Other Examples                             |
       > | ---------------------------------------------------------- | --------------------------------------------- | ---------------------------------- | --------------------------------------- | ------------------------------------------ |
       > | Perl                                                       | 1                                             | "Perl"                             | "Perl"                                  |                                            |
       > | Pe*r*l                                                     | Arbitrary                                     | "Pl"                               | Arbitrary                               | "Pel" "Prl" "Perl" "Peeeeeel" "Peerrrrrrl" |
       > | Full-stop.                                                 | same as number of characters in character set | constant length                    | constant length                         | "Full-stopa" "Full-stopb" "Full-stopc"     |
       > | [1-9] [0-9] [0-9] [0-9]                                    | 9000                                          | constant length                    | constant length                         | "1000" "1001" "1002"                       |
       > | I (love\|hate) programming in (Perl\|Python) and (Java\|C) | 8                                             | "I love programming in Perl and C" | "I love programming in Python and Java" | "I hate programming in Perl and Java"      |

11. This regular expression `[0-9]*.[0-9]*` is intended to match floating point numbers such as '42.5'
    Is it appropriate?

    > No.
    > The regular expression `[0-9]*.[0-9]*` matches strings which are not floating point numbers.
    > It will match zero or more digits, any character, followed by zero or more digits.
    > It also will match numbers such as 01.12
    >
    > A Better expression would be `(0|[1-9][0-9]*)\.([0-9]*[1-9]|0)`

12. What does the command `grep -Ev .` print and why?

    Give an equivalent `grep -E` command with no options,
    in other words: without the `-v`.

    > The pattern `.` matches any character.
    >
    > The option `-v` causes `grep` to print lines which don't match the pattern
    >
    > So the command `grep -Ev .` prints all the empty lines in its input.
    >
    > The command `grep -E '^$'` would also do this.

13. Write a `grep -E` command which will print any lines in a file `ips.txt` containing an IP addresses in the range `129.94.172.1` to `129.94.172.25`

    > ```shell
    > grep -E '129\.94\.172\.([1-9]|1[0-9]|2[0-5])' ips.txt
    > ```

14. For each of the scenarios below

    - give a regular expression to match this class of strings
    - describe the strings being matched using an English sentence

    In the examples, the expected matches are highlighted in bold.

    1. encrypted password fields (including the surrounding colons) in a Unix password file entry, e.g.

       ```
       root:ZHolHAHZw8As2:0:0:root:/root:/bin/bash
       jas:nJz3ru5a/44Ko:100:100:John Shepherd:/home/jas:/bin/zsh
       andrewt:ugGYU6GUJyug2:101:101:Andrew Taylor:/home/jas:/bin/dash
       ```

       > ```
       > :[^:]+:
       > ```
       >
       > Since encrypted passwords can contain just about any character (except colon) you could structure the pattern as "find a colon, followed by a sequence of non-colons, terminated by a colon". Note that this pattern actually matches all of the fields in the line except the first and last, but if we assume that we only look for the first match on each line, it will do.

    2. positive real numbers at the start of a line (using normal fixed-point notation for reals, *not* the kind of scientific notation you find in programming languages), e.g.

       ```
       3.141 value of Pi
       90.57 maximum hits/sec
       half of the time, life is silly
       0.05% is the legal limit
       42 - the meaning of life
       this 1.333 is not at the start
       ```

       > ```
       > ^[0-9]+(\.[0-9]*)?
       > ```
       >
       > This pattern assumes that real numbers will consist of a sequence of digits (the integer part) optionally followed by a decimal point with the fraction digits after the decimal point. Note the use of the `^` symbol to anchor the pattern to the start of the line, the `+` to ensure that there is at least one digit in the integer part, the `\` to escape the special meaning of `.`, and the `?` to make the fractional part optional.

    3. Names as represented in this file containing details of tute/lab enrolments:

       ```
       2134389|Wang, Duved Seo Ken         |fri15-spoons|
       2139656|Undirwaad, Giaffriy Jumis   |tue13-kazoo|
       2154877|Ng, Hinry                   |tue17-kazoo|
       2174328|Zhung, Yung                 |thu17-spoons|
       2234136|Hso, Men-Tsun               |tue09-harp|
       2254148|Khorme, Saneu               |tue09-harp|
       2329667|Mahsin, Zumel               |tue17-kazoo|
       2334348|Trun, Toyin Hong Recky      |mon11-leaf|
       2336212|Sopuvunechyunant, Sopuchue  |mon11-leaf|
       2344749|Chung, Wue Sun              |fri09-harp|
       ...     
       ```

       > ```
       > [^|,]+, [^|]+
       > ```
       >
       > To pick out the content without the delimiters, the first part of the name is any string without a comma or bar, then the comma and space, and then everything up to the next delimiter. Both parts of the name are non-empty, hence `+` is used rather than `*`.

    4. Names as above, but without the trailing spaces (difficult).
       *Hint:* what are given names composed of, and how many of these things can there be?
       
       > ```
       > [^|,]+,( [^| ]+)+
       > ```
       >
       > We couldn't just say `[^| ]+`, because that would disallow spaces inside the given names. For a space to be accepted, it has to be followed by a non-space (usually a letter). Hence the given name portion is one or more sequences of W, where W is a space followed by non-spaces and non-bars.