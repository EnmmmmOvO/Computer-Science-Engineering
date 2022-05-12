#!/bin/sh

#
# This is a simple script to compile and generate
# documentation from the source code

#
# The classes are generated into the current directory
# under the jas and scm packages.

#
# The html documentation is created under reference/jas

# Change this to the full pathname
# if your java compiler or interpreter is not in your path

JAVAC=javac
JAVA=java
JAVADOC=javadoc

JAVAFLAGS=-g

# Compile jas package

mydir=`pwd`

echo "Compiling jas..."
${JAVAC} ${JAVAFLAGS} -d ${mydir} src/jas/*.java

# Compile and run the autogenerator
echo "Compiling autogenerator..."
(cd src/scm; ${JAVAC} -d . autogen/autogen.java)
echo "Creating scm/jas interface..."
(cd src/scm; ${JAVA} autogen)

# Compile scm package

echo "Compiling scm..."
${JAVAC} ${JAVAFLAGS} -d ${mydir} src/scm/*.java

# 
echo "Generating html..."
${JAVADOC} -d reference/jas jas src/jas/*java
echo "Done"
