#include <string>

#include "catch2/catch.hpp"

TEST_CASE("Checks sort3(int&, int&, int&)") {
	auto x = 0;
	auto y = 1;
	auto z = 2;
	REQUIRE(x < y);
	REQUIRE(y < z);

	SECTION("All same object") {
		sort3(x, x, x);
		CHECK(x == 0);
	}

	SECTION("Pre-sorted") {
		sort3(x, y, z);
		CHECK(x < y);
		CHECK(y < z);
	}

	SECTION("Descending") {
		sort3(z, y, x);
		CHECK(z < y);
		CHECK(y < x);
	}

	SECTION("Two same, one different") {
		x = y;
		sort3(x, z, y);
		CHECK(x == z);
		CHECK(x < y);

		sort3(y, x, z);
		CHECK(x == y);
		CHECK(x < z);
	}
}

TEST_CASE("Checks sort3(std::string&, std::string&, std::string&)") {
	auto x = std::string("hello");
	auto y = std::string("there");
	auto z = std::string("world");
	REQUIRE(x < y);
	REQUIRE(y < z);

	SECTION("All same object") {
		sort3(x, x, x);
		CHECK(x == "hello");
	}

	SECTION("Pre-sorted") {
		sort3(x, y, z);
		CHECK(x < y);
		CHECK(y < z);
	}

	SECTION("Descending") {
		sort3(z, y, x);
		CHECK(z < y);
		CHECK(y < x);
	}

	SECTION("Two same, one different") {
		x = y;
		sort3(x, z, y);
		CHECK(x == z);
		CHECK(x < y);

		sort3(y, x, z);
		CHECK(x == y);
		CHECK(x < z);
	}
}
