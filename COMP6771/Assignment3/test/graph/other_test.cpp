#include "gdwg/graph.hpp"

#include <catch2/catch.hpp>

// In this section, I primarily test the operator== and operator<< access section.
//
// For operator==, I test two empty graph, one empty, one normal graph and two normal graph which
// construct with different method.
//
// For operator<<, I test empty graph, it will not show anything. I also test no edge graph and
// normal graph.

TEST_CASE("Test comparisons operator==") {
	SECTION("Test two empty graph") {
		auto g = gdwg::graph<int, int>();
		auto const d = gdwg::graph<int, int>();
		REQUIRE(g == d);
	}

	SECTION("Test normal graph") {
		auto g = gdwg::graph<int, int>{5, 2, 3, 1, 4};
		g.insert_edge(1, 2, 1);
		g.insert_edge(2, 3, 4);
		g.insert_edge(3, 4, 5);
		g.insert_edge(4, 5, 6);

		auto d = gdwg::graph<int, int>();
		d.insert_node(1);
		d.insert_node(2);
		d.insert_node(3);
		d.insert_node(4);
		d.insert_node(5);
		REQUIRE(g != d);
		d.insert_edge(1, 2, 1);
		d.insert_edge(2, 3, 4);
		d.insert_edge(3, 4, 5);
		d.insert_edge(4, 5, 6);
		REQUIRE(g == d);

		auto const e = gdwg::graph<int, int>();
		REQUIRE_FALSE(g == e);
		REQUIRE(g != e);
	}
}

TEST_CASE("Test operator <<") {
	SECTION("Test empty edge and node graph") {
		auto g = gdwg::graph<int, int>();
		std::stringstream string_stream_move;
		string_stream_move << g;
		REQUIRE(string_stream_move.str() == "");
	}

	SECTION("Test no edge graph") {
		auto g = gdwg::graph<int, int>{1, 2, 3};
		std::stringstream string_stream_move;
		string_stream_move << g;
		REQUIRE(string_stream_move.str()
		        == "1 (\n"
		           ")\n"
		           "2 (\n"
		           ")\n"
		           "3 (\n"
		           ")\n");
	}

	SECTION("Test normal graph") {
		auto g = gdwg::graph<int, int>{4, 3, 2, 1, 5, 6, 64};
		g.insert_edge(4, 1, -4);
		g.insert_edge(3, 2, 2);
		g.insert_edge(2, 4, 2);
		g.insert_edge(2, 1, 1);
		g.insert_edge(6, 2, 5);
		g.insert_edge(6, 3, 10);
		g.insert_edge(1, 5, -1);
		g.insert_edge(3, 6, -8);
		g.insert_edge(4, 5, 3);
		g.insert_edge(5, 2, 7);
		std::stringstream string_stream_move;
		string_stream_move << g;
		REQUIRE(string_stream_move.str()
		        == "1 (\n"
		           "  5 | -1\n"
		           ")\n"
		           "2 (\n"
		           "  1 | 1\n"
		           "  4 | 2\n"
		           ")\n"
		           "3 (\n"
		           "  2 | 2\n"
		           "  6 | -8\n"
		           ")\n"
		           "4 (\n"
		           "  1 | -4\n"
		           "  5 | 3\n"
		           ")\n"
		           "5 (\n"
		           "  2 | 7\n"
		           ")\n"
		           "6 (\n"
		           "  2 | 5\n"
		           "  3 | 10\n"
		           ")\n"
		           "64 (\n"
		           ")\n");
	}
}
