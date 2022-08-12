#include <string>
#include <vector>

#include <catch2/catch.hpp>

#include "q1/q1.hpp"

// Please remember to run this file from the project directory
// ./build/test/q1/q1_test1

TEST_CASE("basic test") {
	auto const input = std::vector<std::string>{
		"10 20 sub",
		"4 3 add ",
		"2 mult",
		"16.0 ",
		"2 repeat",
		"sqrt",
		"endrepeat",
		"pop",
		"2.0",
		"mult",
		"3 repeat",
		"2 ",
		"2 reverse",
		"div",
		"3 mult",
		"endrepeat"
	};

	auto output = q1::run_calculator(input);

	auto const expected = std::vector<std::string>{
		"20 - 10 = 10",
		"3 + 4 = 7",
		"2 * 7 = 14",
		"sqrt 16.000 = 4.000",
		"sqrt 4.000 = 2.000",
		"2.000 * 14 = 28.000",
		"28.000 / 2 = 14.000",
		"3 * 14.000 = 42.000",
		"42.000 / 2 = 21.000",
		"3 * 21.000 = 63.000",
		"63.000 / 2 = 31.500",
		"3 * 31.500 = 94.500"
	};

	REQUIRE(expected == output);
}