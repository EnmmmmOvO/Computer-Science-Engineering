#!/usr/bin/python3

# written by andrewt@unsw.edu.au for COMP(2041|9044)
#
# Change the names of the specified files
# by substituting occurrances of regex with replacement
# (simple version of the perl utility rename)
#
# also demonstrating  argument processing and use of eval

# beware eval can allow arbitrary code execution,
# it should not be used where security is importnat


import argparse
import os
import re
import sys

parser = argparse.ArgumentParser()

# add  required arguments
parser.add_argument("regex", type=str, help="match against filenames")
parser.add_argument("replacement", type=str, help="replaces matches with this")
parser.add_argument("filenames", nargs="*", help="filenames to be changed")

# add some optional boolean arguments
parser.add_argument(
    "-d", "--dryrun", action="store_true", help="show changes but don't make them"
)
parser.add_argument(
    "-v", "--verbose", action="store_true", help="print more information"
)
parser.add_argument(
    "-e",
    "--eval",
    action="store_true",
    help="evaluate replacement as python expression, match available as _",
)

# optional integer argument which defaults to 1
parser.add_argument(
    "-n",
    "--replace_n_matches",
    type=int,
    default=1,
    help="replace n matches (0 for all matches)",
)

args = parser.parse_args()


def eval_replacement(match):
    """if --eval given, evaluate replacment string as Python
    with the variable _ set to the matching part of the filename
    """
    if not args.eval:
        return args.replacement
    _ = match.group(0)
    return str(eval(args.replacement))


for old_pathname in args.filenames:
    try:
        new_pathname = re.sub(
            args.regex, eval_replacement, old_pathname, count=args.replace_n_matches
        )
    except OSError as e:
        print(
            f"{sys.argv[0]}: '{old_pathname}': '{args.replacement}'  {e}",
            file=sys.stderr,
        )
        continue

    if new_pathname == old_pathname:
        if args.verbose:
            print("no change:", old_pathname)
        continue

    if os.path.exists(new_pathname):
        print(f"{sys.argv[0]}: '{new_pathname}' exists", file=sys.stderr)
        continue

    if args.dryrun:
        print(old_pathname, "would be renamed to", new_pathname)
        continue

    if args.verbose:
        print("'renaming", old_pathname, "to", new_pathname)
    try:
        os.rename(old_pathname, new_pathname)
    except OSError as e:
        print(f"{sys.argv[0]}: '{new_pathname}' {e}", file=sys.stderr)
