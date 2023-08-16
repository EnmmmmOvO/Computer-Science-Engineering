#!/usr/bin/python3 -u

import os

if os.path.isdir('/dev/null'):
    print('/dev/null')

if os.path.isdir('/dev'):
    print('/dev')
