#!/usr/bin/python3 -u

import subprocess
import sys

subprocess.run(['ls', '-las'] + sys.argv[1:])
