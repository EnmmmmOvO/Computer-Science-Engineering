#include "gdwg/graph.hpp"

#include <catch2/catch.hpp>

// In this section, I primarily test the constructor section.
//
// For empty constructor, two different tests of N and E are done.
//
// For the Initializer List constructor, I used two different types of list inputs, one creating a
// list and passing it into constructor, and the other using {} to prove that it would work in both
// cases. In addition, the situation that the same element exists list is also carried out. Finally,
// there is only one node.
//
// For input iterator constructor, I tested the use of start and end of set vector initializer list.
//
// For graph(graph&& other) and operator=(graph&& other) constructor, because it may include edge
// and node information, I test empty graph, only have node graph and graph with nodes and edges
// situation. The information of after moving graph need to equal with the graph before moving, and
// after moving, the original graph need become empty.
//
// For graph(graph const& other) and operator=(graph const& other) constructor, I also test empty
// graph, only have node graph and graph with nodes and edges situation. To the copy graph have
// same information and store in different memory, I change the original graph information, and
// check they are different.

TEST_CASE("Test empty constructor") {
	SECTION("Test <std::string, int> empty constructor") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE(g.empty());
	}

	SECTION("Test <int, double> empty constructor") {
		auto g = gdwg::graph<int, double>();
		REQUIRE(g.empty());
	}
}

TEST_CASE("Test initializer_list constructor") {
	SECTION("Test int list and confirm it had sorted") {
		auto g = gdwg::graph<int, int>{5, -2, -3, 1, 4};
		REQUIRE(g.nodes() == std::vector<int>{-3, -2, 1, 4, 5});
	}

	SECTION("Test string list and confirm it had sorted") {
		auto string_list = std::initializer_list<std::string>{"how", "are", "you", "today"};
		auto g = gdwg::graph<std::string, int>(string_list);
		REQUIRE(g.nodes() == std::vector<std::string>{"are", "how", "today", "you"});
	}

	SECTION("Test int list with same element, the same element only appear once") {
		auto g = gdwg::graph<int, int>{5, 2, 3, 1, 4, 3};
		REQUIRE(g.nodes() == std::vector<int>{1, 2, 3, 4, 5});
	}
}

TEST_CASE("Test Input iterator constructor") {
	SECTION("Test int vector iterator and confirm it had sorted") {
		auto input_vector = std::vector<int>{3, 5, 1, 9, 4, 7};
		auto g = gdwg::graph<int, int>(input_vector.cbegin(), input_vector.cend());
		REQUIRE(g.nodes() == std::vector<int>{1, 3, 4, 5, 7, 9});
	}

	SECTION("Test double set iterator and confirm it had sorted") {
		auto input_set = std::set<double>{3.3, -4.4, 5.5, -6.6, 7.7, -8.8};
		auto g = gdwg::graph<double, int>(input_set.cbegin(), input_set.cend());
		REQUIRE(g.nodes() == std::vector<double>{-8.8, -6.6, -4.4, 3.3, 5.5, 7.7});
	}

	SECTION("Test std::string initializer_list iterator and confirm it had sorted") {
		auto input_list = std::initializer_list<std::string>{"how", "are", "you", "today", "helen"};
		auto g = gdwg::graph<std::string, int>(input_list.begin(), input_list.end());
		REQUIRE(g.nodes() == std::vector<std::string>{"are", "helen", "how", "today", "you"});
	}
}

TEST_CASE("Test graph(graph&& other) constructor") {
	SECTION("Test move empty graph") {
		auto g = gdwg::graph<std::string, int>();
		auto g_move = gdwg::graph<std::string, int>(std::move(g));
		REQUIRE(g.empty());
		REQUIRE(g_move.empty());
	}

	SECTION("Test move a graph only include node information") {
		auto g = gdwg::graph<int, int>{5, 2, 3, 1, 4};
		std::stringstream string_stream;
		string_stream << g;
		auto g_move = gdwg::graph<int, int>{std::move(g)};
		REQUIRE(g.empty());
		REQUIRE_FALSE(g_move.empty());
		std::stringstream string_stream_move;
		string_stream_move << g_move;
		REQUIRE(string_stream_move.str() == string_stream.str());
		REQUIRE(string_stream_move.str()
		        == "1 (\n"
		           ")\n"
		           "2 (\n"
		           ")\n"
		           "3 (\n"
		           ")\n"
		           "4 (\n"
		           ")\n"
		           "5 (\n"
		           ")\n");
	}

	SECTION("Test move a graph with edge information") {
		auto g = gdwg::graph<int, int>{5, 2, 3, 1, 4};
		g.insert_edge(1, 2, 1);
		g.insert_edge(2, 3, 4);
		g.insert_edge(3, 4, 5);
		g.insert_edge(4, 5, 6);
		std::stringstream string_stream;
		string_stream << g;
		auto g_move = gdwg::graph<int, int>{std::move(g)};
		REQUIRE(g.empty());
		REQUIRE_FALSE(g_move.empty());
		std::stringstream string_stream_move;
		string_stream_move << g_move;
		REQUIRE(string_stream_move.str() == string_stream.str());
		REQUIRE(string_stream_move.str()
		        == "1 (\n"
		           "  2 | 1\n"
		           ")\n"
		           "2 (\n"
		           "  3 | 4\n"
		           ")\n"
		           "3 (\n"
		           "  4 | 5\n"
		           ")\n"
		           "4 (\n"
		           "  5 | 6\n"
		           ")\n"
		           "5 (\n"
		           ")\n");
	}
}

TEST_CASE("Test operator=(graph&& other) constructor") {
	SECTION("Test move empty graph") {
		auto g = gdwg::graph<std::string, int>();
		auto g_move = std::move(g);
		REQUIRE(g.empty());
		REQUIRE(g_move.empty());
	}

	SECTION("Test move a graph only include node information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		std::stringstream string_stream;
		string_stream << g;
		auto g_move = std::move(g);
		REQUIRE(g.empty());
		REQUIRE_FALSE(g_move.empty());
		std::stringstream string_stream_move;
		string_stream_move << g_move;
		REQUIRE(string_stream_move.str() == string_stream.str());
		REQUIRE(string_stream_move.str()
		        == "a (\n"
		           ")\n"
		           "b (\n"
		           ")\n"
		           "c (\n"
		           ")\n"
		           "d (\n"
		           ")\n");
	}

	SECTION("Test move a graph with edge information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "a", 2);
		g.insert_edge("a", "c", 3);
		g.insert_edge("a", "d", 4);
		std::stringstream string_stream;
		string_stream << g;
		auto g_move = std::move(g);
		REQUIRE(g.empty());
		REQUIRE_FALSE(g_move.empty());
		std::stringstream string_stream_move;
		string_stream_move << g_move;
		REQUIRE(string_stream_move.str() == string_stream.str());
		REQUIRE(string_stream_move.str()
		        == "a (\n"
		           "  a | 2\n"
		           "  b | 1\n"
		           "  c | 3\n"
		           "  d | 4\n"
		           ")\n"
		           "b (\n"
		           ")\n"
		           "c (\n"
		           ")\n"
		           "d (\n"
		           ")\n");
	}
}

TEST_CASE("Test graph(graph const& other) constructor") {
	SECTION("Test copy empty graph") {
		auto g = gdwg::graph<std::string, int>();
		auto g_copy = gdwg::graph<std::string, int>(g);
		REQUIRE(g.empty());
		REQUIRE(g_copy.empty());
	}

	SECTION("Test move a graph only include node information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		auto g_copy = gdwg::graph<std::string, int>(g);
		REQUIRE(g == g_copy);
		g.erase_node("a");
		REQUIRE_FALSE(g == g_copy);
		g_copy.erase_node("a");
		REQUIRE(g == g_copy);
	}

	SECTION("Test move a graph with edge information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "a", 2);
		g.insert_edge("a", "c", 3);
		g.insert_edge("a", "d", 4);
		auto g_copy = gdwg::graph<std::string, int>(g);
		REQUIRE(g == g_copy);
		g.erase_edge("a", "b", 1);
		REQUIRE_FALSE(g == g_copy);
		g_copy.erase_edge("a", "b", 1);
		REQUIRE(g == g_copy);
	}
}

TEST_CASE("Test operator=(graph const& other) constructor") {
	SECTION("Test copy empty graph") {
		auto g = gdwg::graph<std::string, int>();
		auto g_move = g;
		REQUIRE(g.empty());
		REQUIRE(g_move.empty());
	}

	SECTION("Test move a graph only include node information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		auto g_copy = g;
		REQUIRE(g == g_copy);
		g.erase_node("a");
		REQUIRE_FALSE(g == g_copy);
		g_copy.erase_node("a");
		REQUIRE(g == g_copy);
	}

	SECTION("Test move a graph with edge information") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "a", 2);
		g.insert_edge("a", "c", 3);
		g.insert_edge("a", "d", 4);
		auto g_copy = g;
		REQUIRE(g == g_copy);
		g.erase_edge("a", "b", 1);
		REQUIRE_FALSE(g == g_copy);
		g_copy.erase_edge("a", "b", 1);
		REQUIRE(g == g_copy);
	}
}
