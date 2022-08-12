#include <catch2/catch.hpp>
#include <vector>

#include "sort_descending.hpp"

TEST_CASE("sort_descending sorts in descending order") {
	SECTION("empty vector") {
		auto v = std::vector<std::string>();
		REQUIRE(v.empty());

		sort_descending(v);
		CHECK(std::is_sorted(v, std::greater{}));
	}

	SECTION("single-element vector") {
		auto v = std::vector<std::string>{"1"};
		REQUIRE(std::distance(v) == 1);

		sort_descending(v);
		CHECK(std::is_sorted(v, std::greater{}));
	}

	SECTION("many elements") {
		auto v = std::vector<std::string>{"36", "84", "122", "76", "41", "19"};
		REQUIRE(std::distance(v) > 1);

		sort_descending(v);
		CHECK(std::is_sorted(v, std::greater{}));
	}
}
