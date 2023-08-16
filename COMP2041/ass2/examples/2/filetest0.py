#!/usr/bin/python3 -u

import os

if os.access('/dev/null', os.R_OK):
    print('a')

if os.access('nonexistantfile', os.R_OK):
    print('b')
