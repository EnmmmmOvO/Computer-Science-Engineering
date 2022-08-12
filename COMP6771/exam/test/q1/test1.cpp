#include <vector>

#include <catch2/catch.hpp>

#include <q1/q1.hpp>

using namespace q1;

TEST_CASE("spec test") {
	const auto styler = style{};
	const auto path = std::vector<q1::move>{
	    move::EE, // go to (1, 0)
        move::SS, // go to (1, 1)
        move::SS, // go to (1, 2)
        move::EE, // go to (2, 2)
        move::NN, // go to (2, 1)
        move::SE, // go to (3, 2)
	};

	const auto mapped = q1::make_map(path, styler);

	CHECK(at(mapped, 3, 2) == '0');
	CHECK(at(mapped, 3, 0) == ' ');
}

TEST_CASE("detailed style test") {
	// won't compile straight away
	const auto styler = detailed_style{'?', '*'};
	const auto path = std::vector<q1::move>{
	    move::SS, // go to (0, 1)
        move::SS, // go to (0, 2)
        move::EE, // go to (1, 2)
        move::EE, // go to (2, 2)
        move::NN, // go to (2, 1)
        move::NN, // go to (2, 0)
        move::SE, // go to (3, 1)
        move::SE, // go to (4, 2)
	};

	const auto mapped = q1::make_map(path, styler);

	CHECK(at(mapped, 0, 0) == '*'); // at this point, 0 moves are made
	CHECK(at(mapped, 0, 1) == 'v');
	CHECK(at(mapped, 0, 2) == '-');
	CHECK(at(mapped, 1, 2) == '>');
	CHECK(at(mapped, 2, 2) == '|');
	CHECK(at(mapped, 2, 1) == '^');
	CHECK(at(mapped, 2, 0) == '\\');
	CHECK(at(mapped, 3, 1) == '\\');
	CHECK(at(mapped, 4, 2) == '*');
}
