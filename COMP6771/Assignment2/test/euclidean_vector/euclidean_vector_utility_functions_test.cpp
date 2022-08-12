#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

// This part mainly tested the functions of Euclidean Vector Utility functions.
//
// For get Euclidean norm, I test empty, one and multi-value. To prove the Caching mechanism, i
// set a function called test_get_euclidean_norm, it will not change anything, it can get
// euclidean_norm which store in the class. Before calculating, it will be -1, because the
// Euclidean norm is square plus square, it must larger than 0, it will not affect the check.
// After calculating, the get_euclidean_norm will get directly from this variable.
//
// For get unit, I test empty, one and multi-value which equal 0's situation, check they will
// throw correct error. I also test one and multi-value which is not equal 0's situation.
//
// For get dot, I test empty, one and multi-value. When the two input vector size is not equal,
// it will throw error.

// Test auto euclidean_norm(euclidean_vector const& v) -> double
TEST_CASE("Test 1: Euclidean norm") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		REQUIRE(comp6771::euclidean_norm(euclidean_vector) == 0);
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{3.3};
		REQUIRE(comp6771::euclidean_norm(euclidean_vector) == 3.3);
	}

	SECTION("Test c: multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, 2.2, 3.3, 4.4};
		REQUIRE(comp6771::euclidean_norm(euclidean_vector) == Approx(6.0249481326));
	}

	SECTION("Test d: multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, -3.3, 5.5, -7.7};
		REQUIRE(comp6771::euclidean_norm(euclidean_vector) == Approx(10.0816665289));
	}

	SECTION("Test e: Caching mechanism") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, -3.3, 5.5, -7.7};
		REQUIRE(euclidean_vector.test_get_euclidean_norm() == -1);
		REQUIRE(comp6771::euclidean_norm(euclidean_vector) == Approx(10.0816665289));
		REQUIRE(euclidean_vector.test_get_euclidean_norm() == Approx(10.0816665289));
	}
}

// Test auto unit(euclidean_vector const& v) -> euclidean_vector
TEST_CASE("Test 2: unit") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		REQUIRE_THROWS_WITH(comp6771::unit(euclidean_vector),
		                    "euclidean_vector with no dimensions "
		                    "does not have a unit vector");
	}

	SECTION("Test b: one value vector, but Euclidean norm is 0") {
		auto const euclidean_vector = comp6771::euclidean_vector{0};
		REQUIRE_THROWS_WITH(comp6771::unit(euclidean_vector),
		                    "euclidean_vector with zero euclidean "
		                    "normal does not have a unit vector");
	}

	SECTION("Test c: one value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{2};
		REQUIRE(comp6771::unit(euclidean_vector)[0] == double{1.0});
	}

	SECTION("Test c: multi-value vector, but Euclidean norm is 0") {
		auto const euclidean_vector = comp6771::euclidean_vector{0, 0, 0, 0, 0};
		REQUIRE_THROWS_WITH(comp6771::unit(euclidean_vector),
		                    "euclidean_vector with zero euclidean "
		                    "normal does not have a unit vector");
	}

	SECTION("Test d: multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{5.7, 3.4, 2.87, -31.4};

		auto const vector_unit = comp6771::unit(euclidean_vector);
		REQUIRE(vector_unit[0] == Approx(0.1768986563));
		REQUIRE(vector_unit[1] == Approx(0.1055184968));
		REQUIRE(vector_unit[2] == Approx(0.0890700252));
		REQUIRE(vector_unit[3] == Approx(-0.9744943524));
	}

	SECTION("Test d: multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, -3.3, 5.5, -7.7};
		auto const vector_unit = comp6771::unit(euclidean_vector);
		REQUIRE(vector_unit[0] == Approx(0.1091089451));
		REQUIRE(vector_unit[1] == Approx(-0.3273268354));
		REQUIRE(vector_unit[2] == Approx(0.5455447256));
		REQUIRE(vector_unit[3] == Approx(-0.7637626158));
	}
}

// Test auto dot(euclidean_vector const& x, euclidean_vector const& y) -> double
TEST_CASE("Test 3: dot") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector(0);
		REQUIRE(comp6771::dot(euclidean_vector_1, euclidean_vector_2) == 0);
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{-4.23222222};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{1.333333333};
		REQUIRE(comp6771::dot(euclidean_vector_1, euclidean_vector_2) == Approx(-5.6429629586));
	}

	SECTION("Test c: two vector with same multi-value") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{-4.23222222, 3.4444, 5.667};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{1.333333333, 3.3, 5.777};
		REQUIRE(comp6771::dot(euclidean_vector_1, euclidean_vector_2) == Approx(38.4618160414));
	}

	SECTION("Test d: two vector with same multi-value") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{1, 2, 3};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{-1, -2, -3};
		REQUIRE(comp6771::dot(euclidean_vector_1, euclidean_vector_2) == double{-14});
	}

	SECTION("Test e: two vector with different size value") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{1, 2, 3, 4};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{-1, -2, -3};
		REQUIRE_THROWS_WITH(comp6771::dot(euclidean_vector_1, euclidean_vector_2),
		                    "Dimensions of LHS(4) and RHS(3) do not match");
	}

	SECTION("Test e: an empty vector and a normal vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector{-1, -2, -3};
		REQUIRE_THROWS_WITH(comp6771::dot(euclidean_vector_1, euclidean_vector_2),
		                    "Dimensions of LHS(0) and RHS(3) do not match");
	}
}