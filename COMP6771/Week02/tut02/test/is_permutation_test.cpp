#include <catch2/catch.hpp>
#include <string>

auto is_permutation(std::string const& x, std::string const& y) -> bool;

TEST_CASE("is_permutation determines if x is a permutation of y") {
	SECTION("1") {
		CHECK(is_permutation("word", "rowd"));
	}
}
