# COMP3311 23T1 Assignment 2 ... Python helper functions
# add any functions to share between Python scripts
# Note: you must submit this file even if you add nothing to it

import re

def clean(s: str) -> str:
    """
    Clean user input
    remove leading and trailing whitespace
    convert to title case (first letter of each word is uppercase, the rest are lowercase)
    squish multiple whitespace characters into a single space
    """
    return re.sub(r'\s+', ' ', s.strip().title())
