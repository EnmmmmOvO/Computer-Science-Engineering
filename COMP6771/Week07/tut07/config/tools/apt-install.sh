#!/bin/bash
# Copyright (c) Christopher Di Bella.
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#
DISTRO=`lsb_release -a 2>&1 | egrep 'Distributor( ID)?:\s+' | cut -d':' -f2 | tr -d '\t'`
CODENAME=`lsb_release -a 2>&1 | egrep 'Codename:\s+' | cut -d':' -f2 | tr -d '\t'`

# We need to know who runs non-root commands
if [[ $1 == "" ]]; then
   echo "$0: ./$0 username"
   echo "`username` should be \"`whoami`\" or \"root\""
   exit 1
fi

if [[ $(id -u) -ne 0 ]]; then
   echo "$0: must be run as root"
   exit 1
fi

if [[ $DISTRO == 'Ubuntu' ]]; then
   GCC10_REPO='ppa:ubuntu-toolchain-r/test'
else
   GCC10_REPO='deb http://deb.debian.org/debian testing main'
fi

install_cmake() {
   if [[ $1 == "root" ]]; then
      python3 -m pip install cmake
   else
      sudo -u $1 python3 -m pip install --user cmake
   fi
}

# Updates system
apt-get update
apt-get dist-upgrade -y
apt-get install -y curl gnupg wget software-properties-common
if [[ $CODENAME != 'focal' ]]; then add-apt-repository "${GCC10_REPO}"; fi
apt-get update

# Installs non-LLVM tools
apt-get install -y  \
    build-essential \
    bzip2           \
    gcc-10          \
    g++-10          \
    gdb             \
    git             \
    gzip            \
    ninja-build     \
    openssh-server  \
    python3         \
    python3-pip     \
    sed             \
    tar             \
    unzip           \
    zip             \
    zlib1g

# Install LLVM
wget https://apt.llvm.org/llvm.sh
chmod +x llvm.sh
sudo ./llvm.sh 11
sudo apt install -y  \
    clang-tidy-11    \
    libc++-11-dev    \
    libc++abi-11-dev \
    python3-clang-11 \

python3 -m pip install pip --upgrade
install_cmake $1

# Regression tests
which gcc-10
which g++-10
which ninja
which cmake
which clang-11
which clangd-11
which clang-format-11
which clang-tidy-11
which lldb-11
which lld-11

dpkg --list | grep libc++-11-dev
dpkg --list | grep libc++abi-11-dev
