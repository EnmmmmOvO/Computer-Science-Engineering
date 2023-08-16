#!/usr/bin/env python3
"""
Simple Python implementation of "make".
Parses makefile rules and stores them in a dict
then builds targets with a recursive function.
written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example
"""

import argparse
import collections
import os
import re
import sys
import subprocess


def main():
    """determine targets to build and build them"""
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--makefile", default="Makefile")
    parser.add_argument("-n", "--dryrun", action="store_true")
    parser.add_argument("build_targets", nargs="*")
    args = parser.parse_args()
    rules = parse_makefile(args.makefile)
    # if not target is specified use first target in Makefile (if any)
    build_targets = args.build_targets or list(rules.keys())[:1]
    for target in build_targets:
        build(target, rules, args.dryrun)


def build(target, rules, dryrun=False):
    """recursively check dependencies and run commands as needed to build target"""
    (dependencies, build_commands) = rules.get(target, ([], []))
    build_needed = not os.path.exists(target)
    for d in dependencies:
        build(d, rules, dryrun)
        build_needed = build_needed or os.path.getmtime(d) > os.path.getmtime(target)
    if not build_needed:
        return
    if not build_commands and not os.path.exists(target):
        print("*** No rule to make target", target)
        sys.exit(1)
    for command in build_commands:
        print(command)
        if not dryrun:
            subprocess.run(command, shell=True)


def parse_makefile(makefile_name):
    """return dict mapping makefile targets to (dependencies, build commands) tuple"""
    rules = collections.OrderedDict()
    with open(makefile_name, encoding="utf-8") as f:
        while line := f.readline():
            if not (m := re.match(r"^(\S+)\s*:\s*(.*)", line)):
                continue
            target = m.group(1)
            dependencies = m.group(2).split()
            build_commands = []
            while (line := f.readline()).startswith("\t"):
                build_commands.append(line.strip())
            rules[target] = (dependencies, build_commands)
    return rules


if __name__ == "__main__":
    main()
