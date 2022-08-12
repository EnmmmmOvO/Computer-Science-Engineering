#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

#include <sstream>

// This part mainly tested the functions of Euclidean Vector Friends.
//
// For equal and not equal operator, I combined them for the test because they are opposites.
// I tested empty vectors, vectors of one data, vectors of multiple data. For vectors of multiple
// data, I tested different data with the same size, the same data, and different sizes
//
// For Addition and Subtraction operation, I test plus/subtraction with same size
// vector and check plus/subtraction with different size vector can throw correct error.
//
// For Multiplication and Division, I try multiply/divide with normal double number,
// and 0 situation. When divide with 0, it will throw error. For the comparison of decimals, I use
// approx to find the approximate value to check.
//
// For Output Stream，I use string stream to check the result. I check the empty vector and no empty
// vector. Although i use std::setprecision to solve the problem that there will be many zeros after
// the decimal point when printing directly, so it can be printed to 10 digits after the decimal
// point at most

// Test bool operator==(euclidean_vector const&, euclidean_vector const&)
// and bool operator!=(euclidean_vector const&, euclidean_vector const&) situation
TEST_CASE("Test 1: Equal and Not Equal") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector(0);
		REQUIRE((euclidean_vector_1 == euclidean_vector_2) == true);
		REQUIRE((euclidean_vector_1 != euclidean_vector_2) == false);
	}

	SECTION("Test b: empty vector and a normal vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector(1);
		REQUIRE((euclidean_vector_1 == euclidean_vector_2) == false);
		REQUIRE((euclidean_vector_1 != euclidean_vector_2) == true);
	}

	SECTION("Test c: two vector have same size and value") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{3, 4.4, 5};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{3, 4.4, 5};
		REQUIRE((euclidean_vector_1 == euclidean_vector_2) == true);
		REQUIRE((euclidean_vector_1 != euclidean_vector_2) == false);
	}

	SECTION("Test d: two vector have same size and different value") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{3, 4.4, 5};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{3, 4.4, 5.5};
		REQUIRE((euclidean_vector_1 == euclidean_vector_2) == false);
		REQUIRE((euclidean_vector_1 != euclidean_vector_2) == true);
	}

	SECTION("Test e: two vector have different size") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{3, 4.4, 5};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{3, 4.4, 5.5};
		REQUIRE((euclidean_vector_1 == euclidean_vector_2) == false);
		REQUIRE((euclidean_vector_1 != euclidean_vector_2) == true);
	}
}

// Test euclidean_vector operator+(euclidean_vector const&, euclidean_vector const&) situation
TEST_CASE("Test 2: Addition") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector(0);
		auto const result = euclidean_vector_1 + euclidean_vector_2;
		REQUIRE(result.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{0};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{1};
		auto const result = euclidean_vector_1 + euclidean_vector_2;
		REQUIRE(result.dimensions() == 1);
		REQUIRE(result[0] == 1);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2)[0] == 1);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2).dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{0, 1, 2};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{7, 3, 1};
		auto const result = euclidean_vector_1 + euclidean_vector_2;
		REQUIRE(result.dimensions() == 3);
		REQUIRE(result[0] == 7);
		REQUIRE(result[1] == 4);
		REQUIRE(result[2] == 3);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2)[0] == 7);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2)[1] == 4);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2)[2] == 3);
		REQUIRE((euclidean_vector_1 + euclidean_vector_2).dimensions() == 3);
	}

	SECTION("Test d: two vector size is not equal") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(3);
		auto euclidean_vector_2 = comp6771::euclidean_vector(4);
		auto result = comp6771::euclidean_vector();
		REQUIRE_THROWS_WITH(result = euclidean_vector_1 + euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(4) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_1 + euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(4) do not match");
	}

	SECTION("Test e: an empty vector and a normal vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto result = comp6771::euclidean_vector();
		REQUIRE_THROWS_WITH(result = euclidean_vector_1 + euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_1 + euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
	}
}

// Test euclidean_vector operator-(euclidean_vector const&, euclidean_vector const&) situation
TEST_CASE("Test 3: Subtraction") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto const euclidean_vector_2 = comp6771::euclidean_vector(0);
		auto const result = euclidean_vector_1 - euclidean_vector_2;
		REQUIRE(result.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{0};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{1};
		auto const result = euclidean_vector_1 - euclidean_vector_2;
		REQUIRE(result.dimensions() == 1);
		REQUIRE(result[0] == -1);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1)[0] == 1);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1).dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto const euclidean_vector_1 = comp6771::euclidean_vector{0, 1, 2};
		auto const euclidean_vector_2 = comp6771::euclidean_vector{7, 3, 1};
		auto const result = euclidean_vector_1 - euclidean_vector_2;
		REQUIRE(result.dimensions() == 3);
		REQUIRE(result[0] == -7);
		REQUIRE(result[1] == -2);
		REQUIRE(result[2] == 1);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1)[0] == 7);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1)[1] == 2);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1)[2] == -1);
		REQUIRE((euclidean_vector_2 - euclidean_vector_1).dimensions() == 3);
	}

	SECTION("Test d: two vector size is not equal") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(3);
		auto euclidean_vector_2 = comp6771::euclidean_vector(4);
		auto result = comp6771::euclidean_vector();
		REQUIRE_THROWS_WITH(result = euclidean_vector_1 - euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(4) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_1 - euclidean_vector_2,
		                    "Dimensions of LHS(3) and RHS(4) do not match");
	}

	SECTION("Test e: an empty vector and a normal vector") {
		auto euclidean_vector_1 = comp6771::euclidean_vector(0);
		auto euclidean_vector_2 = comp6771::euclidean_vector{1.1, 2.2, 3.3};
		auto result = comp6771::euclidean_vector();
		REQUIRE_THROWS_WITH(result = euclidean_vector_1 - euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
		REQUIRE_THROWS_WITH(euclidean_vector_1 - euclidean_vector_2,
		                    "Dimensions of LHS(0) and RHS(3) do not match");
	}
}

// euclidean_vector operator*(euclidean_vector const&, double)
TEST_CASE("Test 4: Subtraction") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		auto double_value = double{1.2};
		auto const result = euclidean_vector * double_value;
		REQUIRE(result.dimensions() == 0);
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{5.5};
		auto double_value = double{1.2};
		auto const result = euclidean_vector * double_value;
		REQUIRE(result.dimensions() == 1);
		REQUIRE(result[0] == 6.6);
		REQUIRE((euclidean_vector * double_value)[0] == 6.6);
		REQUIRE((euclidean_vector * double_value).dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.2, 3.4, 5.6, 7.8};
		auto double_value = double{9.9};
		auto const result = euclidean_vector * double_value;
		REQUIRE(result.dimensions() == 4);
		REQUIRE(result[0] == Approx{11.88});
		REQUIRE(result[1] == Approx{33.66});
		REQUIRE(result[2] == Approx{55.44});
		REQUIRE(result[3] == Approx{77.22});
		REQUIRE((euclidean_vector * double_value).dimensions() == 4);
		REQUIRE((euclidean_vector * double_value)[0] == Approx{11.88});
		REQUIRE((euclidean_vector * double_value)[1] == Approx{33.66});
		REQUIRE((euclidean_vector * double_value)[2] == Approx{55.44});
		REQUIRE((euclidean_vector * double_value)[3] == Approx{77.22});
	}
}

// euclidean_vector operator*(euclidean_vector const&, double)
TEST_CASE("Test 5: Multiply") {
	SECTION("Test a: empty vector (Except 0)") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		auto double_value = double{1.2};
		auto const result = euclidean_vector / double_value;
		REQUIRE(result.dimensions() == 0);
	}

	SECTION("Test b: one value vector (Except 0)") {
		auto const euclidean_vector = comp6771::euclidean_vector{5.5};
		auto double_value = double{1.2};
		auto const result = euclidean_vector / double_value;
		REQUIRE(result.dimensions() == 1);
		REQUIRE(result[0] == Approx{4.5833333333});
		REQUIRE((euclidean_vector / double_value)[0] == Approx{4.5833333333});
		REQUIRE((euclidean_vector / double_value).dimensions() == 1);
	}

	SECTION("Test c: Multi-value vector (Except 0)") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.2, 3.4, 5.6, 7.8};
		auto double_value = double{9.9};
		auto const result = euclidean_vector / double_value;
		REQUIRE(result.dimensions() == 4);
		REQUIRE(result[0] == Approx{0.1212121212});
		REQUIRE(result[1] == Approx{0.3434343434});
		REQUIRE(result[2] == Approx{0.5656565657});
		REQUIRE(result[3] == Approx{0.7878787879});
		REQUIRE((euclidean_vector / double_value).dimensions() == 4);
		REQUIRE((euclidean_vector / double_value)[0] == Approx{0.1212121212});
		REQUIRE((euclidean_vector / double_value)[1] == Approx{0.3434343434});
		REQUIRE((euclidean_vector / double_value)[2] == Approx{0.5656565657});
		REQUIRE((euclidean_vector / double_value)[3] == Approx{0.7878787879});
	}

	SECTION("Test d: a vector divide with 0") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.2, 3.4, 5.6, 7.8};
		auto double_value = double{0};
		auto result = comp6771::euclidean_vector();
		REQUIRE_THROWS_WITH(result = euclidean_vector / double_value, "Invalid vector division by 0");
		REQUIRE_THROWS_WITH(euclidean_vector / double_value, "Invalid vector division by 0");
	}
}

// Test std::ostream& operator<<(std::ostream&, euclidean_vector const&) situation
TEST_CASE("Test 6: Output Stream") {
	SECTION("Test a: empty vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		std::stringstream string_stream;
		string_stream << euclidean_vector;
		REQUIRE(string_stream.str() == "[]");
	}

	SECTION("Test b: one value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1};
		std::stringstream string_stream;
		string_stream << euclidean_vector;
		REQUIRE(string_stream.str() == "[1.1]");
	}

	SECTION("Test c: Multi-value vector (Except 0)") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, -2.2, 3.3, -4.4};
		std::stringstream string_stream;
		string_stream << euclidean_vector;
		REQUIRE(string_stream.str() == "[1.1 -2.2 3.3 -4.4]");
	}
}