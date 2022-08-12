#!/bin/bash
# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
LLVM_VERSION=-11

which git-clang-format${LLVM_VERSION} >/dev/null 2>&1                                        && \
git-clang-format${LLVM_VERSION}           \
   --binary `which clang-format-11`       \
   --style=file                           \
   --extensions c,cc,cpp,cxx,h,hh,hpp,hxx \
   --commit $(git log origin/master..master | grep commit | cut -d' ' -f2 | tr '\n' ' ')
