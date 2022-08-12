#include <catch2/catch.hpp>
#include <iostream>

auto sort_descending(std::vector<int>&) -> void;

TEST_CASE("sort_descending sorts in descending order") {
	SECTION("1"){
		auto number = std::vector<int>{'a', 'b', 'c', 'd', 'e'};
		sort_descending(number);
		CHECK(number == std::vector<int>{'e', 'd', 'c', 'b', 'a'});
	}
}
