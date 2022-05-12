#!/bin/bash
#
# jasmin - runs the Jasmin assembler
# 
# Usage:
#     jasmin [-d ]  [ ...]
#
export CLASSPATH=/Users/enmmmmovo/Documents/Jasmin/classes
echo $CLASSPATH
java jasmin.Main $*