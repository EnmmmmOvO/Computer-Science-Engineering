#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

#include <vector>

// This part mainly tested the functions of Euclidean Vector operations.
//
// For each operation, start with empty vector if is possible(except Subscript, Unary plus,
// Negation), after that test one value and multi-value's situation.
//
// For copy operation, I test changing original vector to prove that both of point to different
// array.
//
// For move operation, I test move a const vector, it will use copy Construct and the
// original will not change.
//
// For Unary plus and Negation operation, I test copy a "+/-euclidean_vector_1", and check
// "+/-euclidean_vector_1 = euclidean_vector_2" and "euclidean_vector_1 = +/-euclidean_vector_2"
//
// For Compound Addition and Compound Subtraction operation, I test plus/subtraction with same size
// vector and check plus/subtraction with different size vector can throw correct error.
//
// For Compound Multiplication and Compound Division, I try multiply/divide with normal double
// number, and 0 situation. When divide with 0, it will throw error. For the comparison of decimals,
// I use approx to find the approximate value to check
//
// For Vector Type Conversion operation, I  checked the specific data in the vector.
// For List Type Conversion operation, I only check the size is correct because of the
// characteristic of std::list;

// Test euclidean_vector& operator=(euclidean_vector const&) situation
TEST_CASE("Test 1: Copy Assignment") {
	SECTION("Test a: Copy empty vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(1);
		auto euclidean_vector_2 = comp6771::euclidean_vector(0);
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_2.dimensions() == 0);

		euclidean_vector_1 = euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 0);
		REQUIRE(euclidean_vector_2.dimensions() == 0);
		REQUIRE(euclidean_vector_1 == euclidean_vector_2);
	}

	SECTION("Test b: Copy default vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector();
		REQUIRE(euclidean_vector_1.dimensions() == 0);
		REQUIRE(euclidean_vector_2.dimensions() == 1);

		euclidean_vector_1 = euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_2.dimensions() == 1);
		REQUIRE(euclidean_vector_1[0] == 0);
		REQUIRE(euclidean_vector_1[0] == 0);
		REQUIRE(euclidean_vector_2 == euclidean_vector_1);
	}

	SECTION("Test c: Copy Multi-value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.0, 2.0, 3.0, 4.0, 5.0};
		REQUIRE(euclidean_vector_1.dimensions() == 3);
		REQUIRE(euclidean_vector_2.dimensions() == 5);

		euclidean_vector_1 = euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 5);
		REQUIRE(euclidean_vector_2.dimensions() == 5);
		REQUIRE(euclidean_vector_1[0] == 1.0);
		REQUIRE(euclidean_vector_1[1] == 2.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_1[3] == 4.0);
		REQUIRE(euclidean_vector_1[4] == 5.0);
		REQUIRE(euclidean_vector_2 == euclidean_vector_1);
	}

	SECTION("Test d: Check the original vector is different with copy vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.0, 2.0, 3.0, 4.0, 5.0};

		euclidean_vector_1 = euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 5);
		REQUIRE(euclidean_vector_2.dimensions() == 5);
		REQUIRE(euclidean_vector_1[0] == 1.0);
		REQUIRE(euclidean_vector_1[1] == 2.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_1[3] == 4.0);
		REQUIRE(euclidean_vector_1[4] == 5.0);
		REQUIRE(euclidean_vector_2 == euclidean_vector_1);

		euclidean_vector_2[0] = -1.0;
		euclidean_vector_2[1] = -2.0;
		euclidean_vector_2[2] = -3.0;

		REQUIRE(euclidean_vector_1[0] == 1.0);
		REQUIRE(euclidean_vector_1[1] == 2.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_1[3] == 4.0);
		REQUIRE(euclidean_vector_1[4] == 5.0);
		REQUIRE(euclidean_vector_1 != euclidean_vector_2);
	}
}

// Test euclidean_vector& operator=(euclidean_vector&&) situation
TEST_CASE("Test 2: Move Assignment") {
	SECTION("Test a: Move empty vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(1);
		auto euclidean_vector_2 = comp6771::euclidean_vector(0);
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_2.dimensions() == 0);

		euclidean_vector_1 = std::move(euclidean_vector_2);
		REQUIRE(euclidean_vector_1.dimensions() == 0);
	}

	SECTION("Test b: Move default vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector();
		REQUIRE(euclidean_vector_1.dimensions() == 0);
		REQUIRE(euclidean_vector_2.dimensions() == 1);

		euclidean_vector_1 = std::move(euclidean_vector_2);
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_1[0] == 0);
		REQUIRE(euclidean_vector_2 != euclidean_vector_1);
	}

	SECTION("Test c: Copy Multi-value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.0, 2.0, 3.0, 4.0, 5.0};
		REQUIRE(euclidean_vector_1.dimensions() == 3);
		REQUIRE(euclidean_vector_2.dimensions() == 5);

		euclidean_vector_1 = std::move(euclidean_vector_2);
		REQUIRE(euclidean_vector_1.dimensions() == 5);
		REQUIRE(euclidean_vector_1[0] == 1.0);
		REQUIRE(euclidean_vector_1[1] == 2.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_1[3] == 4.0);
		REQUIRE(euclidean_vector_1[4] == 5.0);
		REQUIRE(euclidean_vector_2 != euclidean_vector_1);
	}

	SECTION("Test d: Move a const vector, it will use Copy Construct") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{1.0, 2.0, 3.0, 4.0, 5.0};

		euclidean_vector_1 = std::move(euclidean_vector_2);
		REQUIRE(euclidean_vector_1.dimensions() == 5);
		REQUIRE(euclidean_vector_2.dimensions() == 5);
		REQUIRE(euclidean_vector_1[0] == 1.0);
		REQUIRE(euclidean_vector_1[1] == 2.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_1[3] == 4.0);
		REQUIRE(euclidean_vector_1[4] == 5.0);
		REQUIRE(euclidean_vector_2[0] == 1.0);
		REQUIRE(euclidean_vector_2[1] == 2.0);
		REQUIRE(euclidean_vector_2[2] == 3.0);
		REQUIRE(euclidean_vector_2[3] == 4.0);
		REQUIRE(euclidean_vector_2[4] == 5.0);
		REQUIRE(euclidean_vector_2 == euclidean_vector_1);
	}
}

// Test operator[] situation
TEST_CASE("Test 3: Subscript") {
	SECTION("Test a") {
		auto euclidean_vector = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		REQUIRE(euclidean_vector[0] == 1.1);
		REQUIRE(euclidean_vector[1] == 2.2);
		REQUIRE(euclidean_vector[2] == 3.3);
	}

	SECTION("Test b") {
		auto euclidean_vector = comp6771::euclidean_vector(5, 1.1);
		REQUIRE(euclidean_vector[0] == euclidean_vector[1]);
		REQUIRE(euclidean_vector[1] == euclidean_vector[2]);
		REQUIRE(euclidean_vector[4] == euclidean_vector[3]);
		REQUIRE(euclidean_vector[2] == 1.1);
	}
}

// Test euclidean_vector operator+() situation
TEST_CASE("Test 4: Unary plus") {
	SECTION("Test a") {
		auto euclidean_vector = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto euclidean_vector_copy = euclidean_vector;
		REQUIRE(euclidean_vector == euclidean_vector_copy);
		REQUIRE(euclidean_vector == +euclidean_vector_copy);
		REQUIRE(+euclidean_vector == euclidean_vector_copy);
	}

	SECTION("Test b") {
		auto euclidean_vector = comp6771::euclidean_vector(2, 0.01);
		auto euclidean_vector_copy = +euclidean_vector;
		REQUIRE(euclidean_vector_copy[0] == 0.01);
		REQUIRE(euclidean_vector_copy[1] == 0.01);
		REQUIRE(euclidean_vector == +euclidean_vector_copy);
		REQUIRE(+euclidean_vector == euclidean_vector_copy);
	}
}

// Test euclidean_vector operator-() situation
TEST_CASE("Test 5: Negation") {
	SECTION("Test empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		auto euclidean_vector_copy = -euclidean_vector;
		REQUIRE(euclidean_vector == euclidean_vector_copy);
		REQUIRE(euclidean_vector == -euclidean_vector_copy);
		REQUIRE(-euclidean_vector == euclidean_vector_copy);
	}

	SECTION("Test one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{1};
		auto euclidean_vector_copy = -euclidean_vector;
		REQUIRE(euclidean_vector[0] == 1);
		REQUIRE(euclidean_vector_copy[0] == -1);
		REQUIRE(euclidean_vector != euclidean_vector_copy);
		REQUIRE(euclidean_vector == -euclidean_vector_copy);
		REQUIRE(-euclidean_vector == euclidean_vector_copy);
	}

	SECTION("Test Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{1, -1};
		auto euclidean_vector_copy = -euclidean_vector;
		REQUIRE(euclidean_vector[0] == 1);
		REQUIRE(euclidean_vector[1] == -1);
		REQUIRE(euclidean_vector_copy[0] == -1);
		REQUIRE(euclidean_vector_copy[1] == 1);
		REQUIRE(euclidean_vector != euclidean_vector_copy);
		REQUIRE(euclidean_vector == -euclidean_vector_copy);
		REQUIRE(-euclidean_vector == euclidean_vector_copy);
	}

	SECTION("Test Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{1, 2, 3, 4};
		auto euclidean_vector_copy = -euclidean_vector;
		REQUIRE(euclidean_vector[0] == 1);
		REQUIRE(euclidean_vector[1] == 2);
		REQUIRE(euclidean_vector[2] == 3);
		REQUIRE(euclidean_vector[3] == 4);
		REQUIRE(euclidean_vector_copy[0] == -1);
		REQUIRE(euclidean_vector_copy[1] == -2);
		REQUIRE(euclidean_vector_copy[2] == -3);
		REQUIRE(euclidean_vector_copy[3] == -4);
		REQUIRE(euclidean_vector != euclidean_vector_copy);
		REQUIRE(euclidean_vector == -euclidean_vector_copy);
		REQUIRE(-euclidean_vector == euclidean_vector_copy);
	}
}

// Test euclidean_vector& operator+=(euclidean_vector const&) situation
TEST_CASE("Test 6: Compound Addition") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector(0);
		euclidean_vector_1 += euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 0);
		REQUIRE(euclidean_vector_2.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1};
		auto euclidean_vector_2 = comp6771::euclidean_vector{2};
		euclidean_vector_1 += euclidean_vector_2;
		REQUIRE(euclidean_vector_1[0] == 3);
		REQUIRE(euclidean_vector_2[0] == 2);
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_2.dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1, -2, 3, -4};
		auto euclidean_vector_2 = comp6771::euclidean_vector{-1, 2, -3, 4};
		euclidean_vector_1 += euclidean_vector_2;
		REQUIRE(euclidean_vector_1[0] == 0);
		REQUIRE(euclidean_vector_2[0] == -1);
		REQUIRE(euclidean_vector_1[1] == 0);
		REQUIRE(euclidean_vector_2[1] == 2);
		REQUIRE(euclidean_vector_1[2] == 0);
		REQUIRE(euclidean_vector_2[2] == -3);
		REQUIRE(euclidean_vector_1[3] == 0);
		REQUIRE(euclidean_vector_2[3] == 4);
		REQUIRE(euclidean_vector_1.dimensions() == 4);
		REQUIRE(euclidean_vector_2.dimensions() == 4);
	}

	SECTION("Test d: Multi plus operator") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1, 2, 3, 4};
		auto euclidean_vector_2 = comp6771::euclidean_vector(4, 1);
		euclidean_vector_1 += euclidean_vector_2;
		euclidean_vector_2 += euclidean_vector_1;
		euclidean_vector_1 += euclidean_vector_2;
		euclidean_vector_2 += euclidean_vector_1;
		REQUIRE(euclidean_vector_1[0] == 5.0);
		REQUIRE(euclidean_vector_2[0] == 8.0);
		REQUIRE(euclidean_vector_1[1] == 7.0);
		REQUIRE(euclidean_vector_2[1] == 11.0);
		REQUIRE(euclidean_vector_1[2] == 9.0);
		REQUIRE(euclidean_vector_2[2] == 14.0);
		REQUIRE(euclidean_vector_1[3] == 11.0);
		REQUIRE(euclidean_vector_2[3] == 17.0);
		REQUIRE(euclidean_vector_1.dimensions() == 4);
		REQUIRE(euclidean_vector_2.dimensions() == 4);
	}

	SECTION("Test e: two vector size is not equal") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(3);
		auto euclidean_vector_2 = comp6771::euclidean_vector(4);
		REQUIRE_THROWS_WITH(euclidean_vector_1 += euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(4) do not match");
	}

	SECTION("Test f: an empty vector and a normal vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		REQUIRE_THROWS_WITH(euclidean_vector_1 += euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_2 += euclidean_vector_1,
		                    "Dimensions of LHS(3) and RHS(0) do not match");
	}
}

// Test euclidean_vector& operator-=(euclidean_vector const&) situation
TEST_CASE("Test 7: Compound Subtraction") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector(0);
		euclidean_vector_1 -= euclidean_vector_2;
		REQUIRE(euclidean_vector_1.dimensions() == 0);
		REQUIRE(euclidean_vector_2.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{3};
		auto euclidean_vector_2 = comp6771::euclidean_vector{2};
		euclidean_vector_1 -= euclidean_vector_2;
		REQUIRE(euclidean_vector_1[0] == 1);
		REQUIRE(euclidean_vector_2[0] == 2);
		REQUIRE(euclidean_vector_1.dimensions() == 1);
		REQUIRE(euclidean_vector_2.dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1, -2, 3, -4};
		auto euclidean_vector_2 = comp6771::euclidean_vector{-1, 2, -3, 4};
		euclidean_vector_1 -= euclidean_vector_2;
		REQUIRE(euclidean_vector_1[0] == 2);
		REQUIRE(euclidean_vector_2[0] == -1);
		REQUIRE(euclidean_vector_1[1] == -4);
		REQUIRE(euclidean_vector_2[1] == 2);
		REQUIRE(euclidean_vector_1[2] == 6);
		REQUIRE(euclidean_vector_2[2] == -3);
		REQUIRE(euclidean_vector_1[3] == -8);
		REQUIRE(euclidean_vector_2[3] == 4);
		REQUIRE(euclidean_vector_1.dimensions() == 4);
		REQUIRE(euclidean_vector_2.dimensions() == 4);
	}

	SECTION("Test d: Multi subtraction operator") {
		auto euclidean_vector_1 = comp6771::euclidean_vector{1, 2, 3, 4};
		auto euclidean_vector_2 = comp6771::euclidean_vector(4, 1);
		euclidean_vector_1 -= euclidean_vector_2;
		euclidean_vector_2 -= euclidean_vector_1;
		euclidean_vector_1 -= euclidean_vector_2;
		euclidean_vector_2 -= euclidean_vector_1;
		REQUIRE(euclidean_vector_1[0] == -1.0);
		REQUIRE(euclidean_vector_2[0] == 2.0);
		REQUIRE(euclidean_vector_1[1] == 1.0);
		REQUIRE(euclidean_vector_2[1] == -1.0);
		REQUIRE(euclidean_vector_1[2] == 3.0);
		REQUIRE(euclidean_vector_2[2] == -4.0);
		REQUIRE(euclidean_vector_1[3] == 5.0);
		REQUIRE(euclidean_vector_2[3] == -7.0);
		REQUIRE(euclidean_vector_1.dimensions() == 4);
		REQUIRE(euclidean_vector_2.dimensions() == 4);
	}

	SECTION("Test e: two vector size is not equal") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(3);
		auto euclidean_vector_2 = comp6771::euclidean_vector(7);
		REQUIRE_THROWS_WITH(euclidean_vector_1 -= euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(7) do not match");
	}

	SECTION("Test f: an empty vector and a normal vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector{-1.1, -2.2, -3.3};
		REQUIRE_THROWS_WITH(euclidean_vector_1 -= euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_2 -= euclidean_vector_1,
		                    "Dimensions of LHS(3) and RHS(0) do not match");
	}
}

// Test euclidean_vector& operator*=(double) situation
TEST_CASE("Test 7: Compound Multiplication") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		euclidean_vector *= double{0};
		REQUIRE(euclidean_vector.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		euclidean_vector *= double{2};
		REQUIRE(euclidean_vector[0] == 6);
		REQUIRE(euclidean_vector.dimensions() == 1);
	}

	SECTION("Test c: one value vector multiple 0") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		euclidean_vector *= double{0};
		REQUIRE(euclidean_vector[0] == 0);
		REQUIRE(euclidean_vector.dimensions() == 1);
	}

	SECTION("Test d: Multi-value vector multiple positive number") {
		auto euclidean_vector = comp6771::euclidean_vector{1, -2, 3, -4};
		euclidean_vector *= double{2};
		REQUIRE(euclidean_vector[0] == 2);
		REQUIRE(euclidean_vector[1] == -4);
		REQUIRE(euclidean_vector[2] == 6);
		REQUIRE(euclidean_vector[3] == -8);
		REQUIRE(euclidean_vector.dimensions() == 4);
	}

	SECTION("Test e: Multi-value vector multiple 0") {
		auto euclidean_vector = comp6771::euclidean_vector{1, -2, 3, -4};
		euclidean_vector *= double{0};
		REQUIRE(euclidean_vector[0] == 0);
		REQUIRE(euclidean_vector[1] == 0);
		REQUIRE(euclidean_vector[2] == 0);
		REQUIRE(euclidean_vector[3] == 0);
		REQUIRE(euclidean_vector.dimensions() == 4);
	}

	SECTION("Test f: Multi-value vector multiple negative number") {
		auto euclidean_vector = comp6771::euclidean_vector{1.1, -2.2, 3.3, -4.4};
		euclidean_vector *= double{-2.1};
		REQUIRE(euclidean_vector[0] == Approx(-2.31));
		REQUIRE(euclidean_vector[1] == Approx(4.62));
		REQUIRE(euclidean_vector[2] == Approx(-6.93));
		REQUIRE(euclidean_vector[3] == Approx(9.24));
		REQUIRE(euclidean_vector.dimensions() == 4);
	}
}

// Test euclidean_vector& operator/=(double) situation
TEST_CASE("Test 8: Compound Division") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		euclidean_vector /= double{1};
		REQUIRE(euclidean_vector.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		euclidean_vector /= double{1.5};
		REQUIRE(euclidean_vector[0] == 2);
		REQUIRE(euclidean_vector.dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector multiple positive number") {
		auto euclidean_vector = comp6771::euclidean_vector{1, -2, 3, -4};
		euclidean_vector /= double{2};
		REQUIRE(euclidean_vector[0] == 0.5);
		REQUIRE(euclidean_vector[1] == -1);
		REQUIRE(euclidean_vector[2] == 1.5);
		REQUIRE(euclidean_vector[3] == -2);
		REQUIRE(euclidean_vector.dimensions() == 4);
	}

	SECTION("Test d: Multi-value vector multiple negative number") {
		auto euclidean_vector = comp6771::euclidean_vector{1.1, -2.2, 3.3, -4.4};
		euclidean_vector /= double{-2.1};
		REQUIRE(euclidean_vector[0] == Approx(-0.5238095238));
		REQUIRE(euclidean_vector[1] == Approx(1.0476190476));
		REQUIRE(euclidean_vector[2] == Approx(-1.5714285714));
		REQUIRE(euclidean_vector[3] == Approx(2.0952380952));
		REQUIRE(euclidean_vector.dimensions() == 4);
	}

	SECTION("Test e: Multi-value vector multiple 0") {
		auto euclidean_vector = comp6771::euclidean_vector{1, -2, 3, -4};
		REQUIRE_THROWS_WITH(euclidean_vector /= double{0}, "Invalid vector division by 0");
	}

	SECTION("Test f: empty vector multiple 0") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		REQUIRE_THROWS_WITH(euclidean_vector /= double{0}, "Invalid vector division by 0");
	}
}

// Test operator std::vector<double>() situation
TEST_CASE("Test 9: Vector Type Conversion") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		auto const vector = static_cast<std::vector<double>>(euclidean_vector);
		REQUIRE(vector.empty() == true);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		auto const vector = static_cast<std::vector<double>>(euclidean_vector);
		REQUIRE(vector[0] == 3);
		REQUIRE(vector.size() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3, 4, 5, 6.6};
		auto const vector = static_cast<std::vector<double>>(euclidean_vector);
		REQUIRE(vector[0] == 3);
		REQUIRE(vector[1] == 4);
		REQUIRE(vector[2] == 5);
		REQUIRE(vector[3] == 6.6);
		REQUIRE(vector.size() == 4);
	}
}

// Test operator std::list<double>() situation
TEST_CASE("Test 10: List Type Conversion") {
	SECTION("Test a: empty vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		auto const list = static_cast<std::list<double>>(euclidean_vector);
		REQUIRE(list.empty() == true);
	}

	SECTION("Test b: one value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3};
		auto const list = static_cast<std::list<double>>(euclidean_vector);
		REQUIRE(list.size() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{3, 4, 5, 6.6};
		auto const list = static_cast<std::list<double>>(euclidean_vector);
		REQUIRE(list.size() == 4);
	}
}