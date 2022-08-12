# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
FROM ubuntu:20.04

# Updates system
RUN apt-get update
RUN apt-get dist-upgrade -y
RUN apt-get install -y curl gnupg wget software-properties-common
RUN apt-get update

# Installs non-LLVM tools
RUN apt-get install -y \
    build-essential \
    bzip2           \
    cmake           \
    gcc-10          \
    g++-10          \
    gdb             \
    git             \
    gzip            \
    ninja-build     \
    openssh-server  \
    sed             \
    tar             \
    unzip           \
    zip             \
    zlib1g

# Install LLVM
RUN wget https://apt.llvm.org/llvm.sh
RUN chmod +x llvm.sh
RUN ./llvm.sh 11
RUN apt-get install -y  \
    clang-tidy-11    \
    libc++-11-dev    \
    libc++abi-11-dev \
    python3-clang-11


WORKDIR /
RUN apt-get remove -y software-properties-common
RUN apt-get dist-upgrade -y
RUN apt-get autoremove -y
