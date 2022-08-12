#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

#include <vector>

// This part mainly tested the functions of Euclidean Vector construction.
//
// For each constructor, start with empty vector if is possible (except Default Constructor
// and List Constructor), after that test one value and multi-value's situation.
// For copy and move constructor, I test copy or move itself, and it will remain unchanged.
// For copy constructor, I test changing original vector to prove that both of point to different
// array.
// For move constructor, I also test move a const vector, it will use copy Construct and the
// original will not change.

// Test euclidean_vector() situation
TEST_CASE("Test 1: Default Constructor") {
	auto const euclidean_vector = comp6771::euclidean_vector();
	REQUIRE(euclidean_vector.dimensions() == 1);
	REQUIRE(euclidean_vector[0] == 0.0);
}

// Test euclidean_vector(int) situation
TEST_CASE("Test 2: Single-argument Constructor") {
	SECTION("Test Empty euclidean vector situation") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		REQUIRE(euclidean_vector.dimensions() == 0);
	}

	SECTION("Test One dimension situation") {
		auto const euclidean_vector = comp6771::euclidean_vector(1);
		REQUIRE(euclidean_vector.dimensions() == 1);
		REQUIRE(euclidean_vector[0] == 0.0);
	}

	SECTION("Test Multi-dimension situation") {
		auto const euclidean_vector = comp6771::euclidean_vector(3);
		REQUIRE(euclidean_vector.dimensions() == 3);
		REQUIRE(euclidean_vector[0] == 0.0);
		REQUIRE(euclidean_vector[1] == 0.0);
		REQUIRE(euclidean_vector[2] == 0.0);
	}
}

// Test euclidean_vector(int, double) situation
TEST_CASE("Test 3: An integer and a double dimension argument Constructor") {
	SECTION("Test a: An integer (3) and a positive double (1.1) dimension situation") {
		auto const euclidean_vector = comp6771::euclidean_vector(3, 1.1);
		REQUIRE(euclidean_vector.dimensions() == 3);
		REQUIRE(euclidean_vector[0] == 1.1);
		REQUIRE(euclidean_vector[1] == 1.1);
		REQUIRE(euclidean_vector[2] == 1.1);
	}

	SECTION("Test b: An integer (5) and a negative double (-2.2) dimension situation") {
		auto const euclidean_vector = comp6771::euclidean_vector(3, -2.2);
		REQUIRE(euclidean_vector.dimensions() == 3);
		REQUIRE(euclidean_vector[0] == -2.2);
		REQUIRE(euclidean_vector[1] == -2.2);
		REQUIRE(euclidean_vector[2] == -2.2);
	}

	SECTION("Test c: Assign two variables and construct with two variables") {
		auto dimension = int{2};
		auto value = double{3.0};
		auto const euclidean_vector = comp6771::euclidean_vector(dimension, value);
		REQUIRE(euclidean_vector.dimensions() == 2);
		REQUIRE(euclidean_vector[0] == 3.0);
		REQUIRE(euclidean_vector[1] == 3.0);
	}
}

// Test euclidean_vector(std::vector<double>::const_iterator, std::vector<double>::const_iterator)
// situation
TEST_CASE("Test 4: A vector begin iterator and a vector end iterator argument Constructor") {
	SECTION("Test a: Empty value in Vector") {
		auto vector = std::vector<double>{};
		auto const euclidean_vector = comp6771::euclidean_vector(vector.cbegin(), vector.cend());
		REQUIRE(euclidean_vector.dimensions() == 0);
	}

	SECTION("Test b: Same value in Vector") {
		auto vector = std::vector<double>(3, 3.0);
		auto const euclidean_vector = comp6771::euclidean_vector(vector.cbegin(), vector.cend());
		REQUIRE(euclidean_vector.dimensions() == 3);
		REQUIRE(euclidean_vector[0] == 3.0);
		REQUIRE(euclidean_vector[1] == 3.0);
		REQUIRE(euclidean_vector[2] == 3.0);
	}

	SECTION("Test c: Different value in Vector") {
		auto vector = std::vector<double>{1.1, -2.2, 3.3};
		auto const euclidean_vector = comp6771::euclidean_vector(vector.cbegin(), vector.cend());
		REQUIRE(euclidean_vector.dimensions() == 3);
		REQUIRE(euclidean_vector[0] == 1.1);
		REQUIRE(euclidean_vector[1] == -2.2);
		REQUIRE(euclidean_vector[2] == 3.3);
	}
}

// Test euclidean_vector(std::initializer_list<double>) situation
TEST_CASE("Test 5: A initializer_list argument Constructor") {
	SECTION("Test a: Empty list in Vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{};
		REQUIRE(euclidean_vector.dimensions() == 1);
		REQUIRE(euclidean_vector[0] == 0.0);
	}

	SECTION("Test b: Multi-value in Vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{1.1, -3.3, 5.5, -7.7};
		REQUIRE(euclidean_vector.dimensions() == 4);
		REQUIRE(euclidean_vector[0] == 1.1);
		REQUIRE(euclidean_vector[1] == -3.3);
		REQUIRE(euclidean_vector[2] == 5.5);
		REQUIRE(euclidean_vector[3] == -7.7);
	}
}

// Test euclidean_vector(euclidean_vector const&) situation
TEST_CASE("Test 6: Copy Constructor situation") {
	SECTION("Test a: Copy Empty euclidean vector") {
		auto const euclidean_vector = comp6771::euclidean_vector(0);
		auto const euclidean_vector_copy = comp6771::euclidean_vector(euclidean_vector);
		REQUIRE(euclidean_vector.dimensions() == 0);
		REQUIRE(euclidean_vector_copy.dimensions() == 0);
	}

	SECTION("Test b: Copy default vector") {
		auto const euclidean_vector = comp6771::euclidean_vector();
		auto const euclidean_vector_copy = comp6771::euclidean_vector(euclidean_vector);
		REQUIRE(euclidean_vector.dimensions() == 1);
		REQUIRE(euclidean_vector_copy.dimensions() == 1);
		REQUIRE(euclidean_vector[0] == 0);
		REQUIRE(euclidean_vector_copy[0] == 0);
	}

	SECTION("Test c: Copy Multi--value vector") {
		auto const euclidean_vector = comp6771::euclidean_vector{13.1, 11.3, 9.5, 7.7, 5.9};
		auto const euclidean_vector_copy = comp6771::euclidean_vector(euclidean_vector);
		REQUIRE(euclidean_vector.dimensions() == 5);
		REQUIRE(euclidean_vector_copy.dimensions() == 5);
		REQUIRE(euclidean_vector[0] == 13.1);
		REQUIRE(euclidean_vector_copy[0] == 13.1);
		REQUIRE(euclidean_vector[1] == 11.3);
		REQUIRE(euclidean_vector_copy[1] == 11.3);
		REQUIRE(euclidean_vector[2] == 9.5);
		REQUIRE(euclidean_vector_copy[2] == 9.5);
		REQUIRE(euclidean_vector[3] == 7.7);
		REQUIRE(euclidean_vector_copy[3] == 7.7);
		REQUIRE(euclidean_vector[4] == 5.9);
		REQUIRE(euclidean_vector_copy[4] == 5.9);
	}

	SECTION("Test d: Check the original vector is different with copy vector") {
		auto euclidean_vector = comp6771::euclidean_vector{13.1, 11.3};
		auto euclidean_vector_copy = comp6771::euclidean_vector(euclidean_vector);
		REQUIRE(euclidean_vector.dimensions() == 2);
		REQUIRE(euclidean_vector_copy.dimensions() == 2);
		REQUIRE(euclidean_vector[0] == 13.1);
		REQUIRE(euclidean_vector_copy[0] == 13.1);
		REQUIRE(euclidean_vector[1] == 11.3);
		REQUIRE(euclidean_vector_copy[1] == 11.3);

		// Change the original vector
		euclidean_vector[0] = -13.1;
		euclidean_vector[1] = -11.3;
		REQUIRE(euclidean_vector[0] == -13.1);
		REQUIRE(euclidean_vector_copy[0] == 13.1);
		REQUIRE(euclidean_vector[0] != euclidean_vector_copy[0]);
		REQUIRE(euclidean_vector[1] == -11.3);
		REQUIRE(euclidean_vector_copy[1] == 11.3);
		REQUIRE(euclidean_vector[1] != euclidean_vector_copy[1]);

		// Change the copy vector
		euclidean_vector_copy[0] = -1.1;
		euclidean_vector_copy[1] = -1.3;
		REQUIRE(euclidean_vector_copy[0] == -1.1);
		REQUIRE(euclidean_vector_copy[1] == -1.3);
	}
}

// Test euclidean_vector(euclidean_vector&&) situation
TEST_CASE("Test 7: Move Constructor situation") {
	SECTION("Test a: Move Empty euclidean vector") {
		auto euclidean_vector = comp6771::euclidean_vector(0);
		auto const euclidean_vector_move = comp6771::euclidean_vector(std::move(euclidean_vector));
		REQUIRE(euclidean_vector_move.dimensions() == 0);
	}

	SECTION("Test a: Move a default euclidean vector") {
		auto euclidean_vector = comp6771::euclidean_vector();
		auto const euclidean_vector_move = comp6771::euclidean_vector(std::move(euclidean_vector));
		REQUIRE(euclidean_vector_move.dimensions() == 1);
		REQUIRE(euclidean_vector.dimensions() == 0);
		REQUIRE(euclidean_vector != euclidean_vector_move);
	}

	SECTION("Test c: Move Multi--value vector") {
		auto euclidean_vector = comp6771::euclidean_vector{13.1, 11.3, 9.5, 7.7, 5.9};
		auto const euclidean_vector_move = comp6771::euclidean_vector(std::move(euclidean_vector));
		REQUIRE(euclidean_vector.dimensions() == 0);
		REQUIRE(euclidean_vector_move.dimensions() == 5);
		REQUIRE(euclidean_vector_move[0] == 13.1);
		REQUIRE(euclidean_vector_move[1] == 11.3);
		REQUIRE(euclidean_vector_move[2] == 9.5);
		REQUIRE(euclidean_vector_move[3] == 7.7);
		REQUIRE(euclidean_vector_move[4] == 5.9);
		REQUIRE(euclidean_vector != euclidean_vector_move);
	}

	SECTION("Test c: Move Same Vector") {
		auto euclidean_vector = comp6771::euclidean_vector{13.1, 11.3, 9.5, 7.7, 5.9};
		euclidean_vector = comp6771::euclidean_vector(std::move(euclidean_vector));
		REQUIRE(euclidean_vector.dimensions() == 5);
		REQUIRE(euclidean_vector[0] == 13.1);
		REQUIRE(euclidean_vector[1] == 11.3);
		REQUIRE(euclidean_vector[2] == 9.5);
		REQUIRE(euclidean_vector[3] == 7.7);
		REQUIRE(euclidean_vector[4] == 5.9);
	}

	SECTION("Test d: Move a const vector, it will use Copy Construct") {
		auto const euclidean_vector = comp6771::euclidean_vector{13.1, 11.3, 9.5, 7.7, 5.9};
		auto const euclidean_vector_move = comp6771::euclidean_vector(std::move(euclidean_vector));
		REQUIRE(euclidean_vector.dimensions() == 5);
		REQUIRE(euclidean_vector_move.dimensions() == 5);
		REQUIRE(euclidean_vector[0] == 13.1);
		REQUIRE(euclidean_vector_move[0] == 13.1);
		REQUIRE(euclidean_vector[1] == 11.3);
		REQUIRE(euclidean_vector_move[1] == 11.3);
		REQUIRE(euclidean_vector[2] == 9.5);
		REQUIRE(euclidean_vector_move[2] == 9.5);
		REQUIRE(euclidean_vector[3] == 7.7);
		REQUIRE(euclidean_vector_move[3] == 7.7);
		REQUIRE(euclidean_vector[4] == 5.9);
		REQUIRE(euclidean_vector_move[4] == 5.9);
		REQUIRE(euclidean_vector == euclidean_vector_move);
	}
}