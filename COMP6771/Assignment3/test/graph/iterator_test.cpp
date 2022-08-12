#include "gdwg/graph.hpp"

#include <catch2/catch.hpp>

// In this section, I primarily test the iterator and iterator access section.
//
// For this part, we mainly test the iterator in operator++, operator--, getting the reference of
// operator*. and for g.begin() and g.end().
//
// For operator-, if it = g.end(), the --it will become the last weight between last src and dst.

TEST_CASE("Test *operator") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	g.insert_edge(2, 3, 4);
	auto it = g.begin();
	auto temp = *it;
	REQUIRE(temp.from == 1);
	REQUIRE(temp.to == 2);
	REQUIRE(temp.weight == 1);
	++it;
	temp = *it;
	REQUIRE(temp.from == 2);
	REQUIRE(temp.to == 3);
	REQUIRE(temp.weight == 4);
}

TEST_CASE("Test operator++") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	g.insert_edge(2, 3, 4);
	auto it = g.begin();
	auto temp = *it;
	REQUIRE(temp.from == 1);
	REQUIRE(temp.to == 2);
	REQUIRE(temp.weight == 1);
	++it;
	temp = *it;
	REQUIRE(temp.from == 2);
	REQUIRE(temp.to == 3);
	REQUIRE(temp.weight == 4);
	++it;
	REQUIRE(it == g.end());
}

TEST_CASE("Test operator--") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	g.insert_edge(2, 3, 4);
	auto it = g.end();
	REQUIRE(it == g.end());
	--it;
	auto temp = *it;
	REQUIRE(temp.from == 2);
	REQUIRE(temp.to == 3);
	REQUIRE(temp.weight == 4);
	--it;
	temp = *it;
	REQUIRE(temp.from == 1);
	REQUIRE(temp.to == 2);
	REQUIRE(it == g.begin());
}

TEST_CASE("Test operator==") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	auto it = g.end();
	REQUIRE(it == g.end());
	--it;
	REQUIRE(it == g.begin());
}

TEST_CASE("Test begin() const") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	auto it = g.begin();
	auto temp = *it;
	REQUIRE(temp.from == 1);
	REQUIRE(temp.to == 2);
	REQUIRE(temp.weight == 1);
}

TEST_CASE("Test end() const") {
	auto g = gdwg::graph<int, int>{1, 2, 3};
	g.insert_edge(1, 2, 1);
	auto it = g.begin();
	++it;
	REQUIRE(it == g.end());
}
