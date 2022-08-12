// Copyright (c) Hayden Smith
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
#include <string>

#include "catch2/catch.hpp"

TEST_CASE("Hello, C++!") {
	int num1 = 5;
	int num2 = 4;
	CHECK((num1 + num2) == 9);
}
