#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

// This part mainly tested the functions of Euclidean Vector Member Functions.
//
// For const at and non-const at test, I test empty vector, and it will throw error whatever index
// is. I also test one and multi value situation. For non-const test, I also test change the
// corresponding position's data.
//
// For dimensions, I test empty, one value and multi-value situation.

// Test double at(int) const situation
TEST_CASE("Test 1: at const") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		auto index = double{0};
		REQUIRE_THROWS_WITH(index = euclidean_vector.at(0),
		                    "Index 0 is not valid for this euclidean_vector object");
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{3};
		REQUIRE(euclidean_vector.at(0) == 3);
		auto index = double{0};
		REQUIRE_THROWS_WITH(index = euclidean_vector.at(-1),
		                    "Index -1 is not valid for this euclidean_vector object");
	}

	SECTION("Test c: Multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{3, 4.4, 5};
		REQUIRE(euclidean_vector.at(0) == 3);
		REQUIRE(euclidean_vector.at(1) == 4.4);
		REQUIRE(euclidean_vector.at(2) == 5);
	}
}

// Test double& at(int) situation
TEST_CASE("Test 2: at") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		auto index = double{0};
		REQUIRE_THROWS_WITH(index = euclidean_vector.at(0),
		                    "Index 0 is not valid for this euclidean_vector object");
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		REQUIRE(euclidean_vector.at(0) == 3);
		euclidean_vector.at(0) = 2;
		REQUIRE(euclidean_vector.at(0) == 2);
		auto index = double{0};
		REQUIRE_THROWS_WITH(index = euclidean_vector.at(100),
		                    "Index 100 is not valid for this euclidean_vector object");
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3, 4.4, 5};
		REQUIRE(euclidean_vector.at(0) == 3);
		REQUIRE(euclidean_vector.at(1) == 4.4);
		REQUIRE(euclidean_vector.at(2) == 5);
		euclidean_vector.at(0) = 1.1;
		euclidean_vector.at(1) = 2.2;
		euclidean_vector.at(2) = 3.3;
		REQUIRE(euclidean_vector.at(0) == 1.1);
		REQUIRE(euclidean_vector.at(1) == 2.2);
		REQUIRE(euclidean_vector.at(2) == 3.3);
	}
}

// Test int dimensions() situation
TEST_CASE("Test 3: dimensions") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		REQUIRE(euclidean_vector.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		REQUIRE(euclidean_vector.dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{1, 2, 3, 4, 5, 6, 7, 8};
		REQUIRE(euclidean_vector.dimensions() == 8);
	}
}