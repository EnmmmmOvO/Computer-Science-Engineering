#include <string>

#include "../source/sort3.cpp"
#include "catch2/catch.hpp"

TEST_CASE("sort3 for integers") {
	auto a = 3;
	auto b = 2;
	auto c = 1;

	SECTION("1") {
		sort3(a, b, c);
		CHECK(a < b);
		CHECK(b < c);
		CHECK(a < c);
	}
}
TEST_CASE("sort3 for std::string") {
	std::string a = "count";
	std::string b = "boy";
	std::string c = "apple";


	SECTION("1") {
		sort3(a, b, c);
		CHECK(a < b);
		CHECK(b < c);
		CHECK(a < c);
	}
}
