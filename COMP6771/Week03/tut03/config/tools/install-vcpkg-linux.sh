#!/bin/bash

set -e

if [[ ! -f "${PWD}/config/tools/install-vcpkg-linux.sh" ]]; then
	echo "This script needs to be run from the top-level directory of the project."
	exit 1
fi

if [[ ! -d ./vcpkg ]]; then
	git clone https://github.com/Microsoft/vcpkg.git
fi

cd vcpkg
git pull
./bootstrap-vcpkg.sh -disableMetrics
cp ../config/cmake/triplets/* triplets/community/.
./vcpkg install --clean-after-build catch2:x64-linux-libcxx
cd ..
sed -i 's#/import/kamen/1/cs6771#${workspaceFolder}#' .vscode/cmake-kits.json
