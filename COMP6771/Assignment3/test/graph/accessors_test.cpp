#include "gdwg/graph.hpp"

#include <catch2/catch.hpp>

// In this section, I primarily test the modifiers section.
//
// For all the function, I test const and non const graph and confirm both of them can use.
//
// For is_node and empty function, I test empty graph, normal graph.
//
// For is_connected function, I try check connected with itself, other node, and the node which is
// not existed.
//
// For nodes, weight and connection function, I try return empty vector, normal vector. When src or
// dst is not existed, the weights and connections will throw runtime_error.
//
// For find function, I test find in empty graph, find the src or dst or weight is not existed
// situation, all return g.end().

TEST_CASE("Test is_node function") {
	SECTION("Test empty graph") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE_FALSE(g.is_node("a"));
	}

	SECTION("Test non const graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		REQUIRE(g.is_node("a"));
		REQUIRE(g.is_node("b"));
		REQUIRE(g.is_node("c"));
		REQUIRE_FALSE(g.is_node("e"));
	}

	SECTION("Test const graph") {
		auto const g = gdwg::graph<std::string, int>{"a", "b", "c"};
		REQUIRE(g.is_node("a"));
		REQUIRE(g.is_node("b"));
		REQUIRE(g.is_node("c"));
		REQUIRE_FALSE(g.is_node("e"));
	}
}

TEST_CASE("Test empty function") {
	SECTION("Test non const graph") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE(g.empty());
		auto d = gdwg::graph<std::string, int>{"1"};
		REQUIRE_FALSE(d.empty());
	}

	SECTION("Test const graph") {
		auto const g = gdwg::graph<std::string, int>();
		REQUIRE(g.empty());
		auto const d = gdwg::graph<std::string, int>{"1"};
		REQUIRE_FALSE(d.empty());
	}
}

TEST_CASE("Test is_connected function") {
	SECTION("Test non const graph, src and dst existed") {
		auto d = gdwg::graph<std::string, int>{"1"};
		REQUIRE_FALSE(d.is_connected("1", "1"));
		d.insert_edge("1", "1", 1);
		REQUIRE(d.is_connected("1", "1"));
	}

	SECTION("Test const graph, src and dst existed") {
		auto d = gdwg::graph<std::string, int>{"1"};
		auto const p = d;
		REQUIRE_FALSE(p.is_connected("1", "1"));
		d.insert_edge("1", "1", 1);
		auto const a = d;
		REQUIRE(a.is_connected("1", "1"));
	}

	SECTION("Test src and dst is not existed") {
		auto d = gdwg::graph<std::string, int>{"1"};
		auto temp = bool{true};
		REQUIRE_THROWS(temp = d.is_connected("2", "1"),
		               "Cannot call gdwg::graph<N, E>::"
		               "is_connected if src or dst node don't "
		               "exist in the graph");
		REQUIRE_THROWS(temp = d.is_connected("1", "2"),
		               "Cannot call gdwg::graph<N, E>::"
		               "is_connected if src or dst node don't "
		               "exist in the graph");
	}
}

TEST_CASE("Test nodes function") {
	SECTION("Test empty graph") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE(g.nodes() == std::vector<std::string>());
		auto const b = gdwg::graph<std::string, int>();
		REQUIRE(b.nodes() == std::vector<std::string>());
	}

	SECTION("Test normal graph and check the vector had been sorted") {
		auto g = gdwg::graph<std::string, int>{"b", "a", "c"};
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b", "c"});
		auto const b = gdwg::graph<std::string, int>{"b", "a", "c"};
		REQUIRE(b.nodes() == std::vector<std::string>{"a", "b", "c"});
	}
}

TEST_CASE("Test weights function") {
	SECTION("test empty edge graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.weights("a", "a") == std::vector<int>());
		REQUIRE(g.weights("a", "b") == std::vector<int>());
		auto const d = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(d.weights("a", "a") == std::vector<int>());
		REQUIRE(d.weights("a", "b") == std::vector<int>());
	}

	SECTION("test normal edge graph, src and dst existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE(g.weights("a", "a") == std::vector<int>{3, 4});
		REQUIRE(g.weights("a", "b") == std::vector<int>{1, 2});
		auto const d = g;
		REQUIRE(d.weights("a", "a") == std::vector<int>{3, 4});
		REQUIRE(d.weights("a", "b") == std::vector<int>{1, 2});
	}

	SECTION("src and dst is not existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		auto temp = std::vector<int>();
		REQUIRE_THROWS(temp = g.weights("a", "c"),
		               "Cannot call gdwg::"
		               "graph<N, E>::weights if src or dst"
		               " node don't exist in the graph");
		auto const d = g;
		REQUIRE_THROWS(temp = d.weights("c", "a"),
		               "Cannot call gdwg::"
		               "graph<N, E>::weights if src or dst"
		               " node don't exist in the graph");
	}
}

TEST_CASE("Test find function") {
	SECTION("find in empty graph") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE(g.find("a", "b", 1) == g.end());
		auto const d = gdwg::graph<std::string, int>();
		REQUIRE(d.find("a", "b", 1) == d.end());
	}

	SECTION("find in normal graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		auto temp = *g.find("b", "a", 1);
		REQUIRE(temp.from == "b");
		REQUIRE(temp.to == "a");
		REQUIRE(temp.weight == 1);
		REQUIRE(g.find("b", "a", 5) == g.end());
		auto const d = g;
		temp = *d.find("a", "a", 3);
		REQUIRE(temp.from == "a");
		REQUIRE(temp.to == "a");
		REQUIRE(temp.weight == 3);
		REQUIRE(d.find("a", "a", 5) == d.end());
	}
}

TEST_CASE("Test connections function") {
	SECTION("check in no edge graph") {
		auto g = gdwg::graph<std::string, int>{"a"};
		REQUIRE(g.connections("a") == std::vector<std::string>());
		auto const d = gdwg::graph<std::string, int>{"a"};
		REQUIRE(d.connections("a") == std::vector<std::string>());
	}

	SECTION("check in normal graph, src is existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "e"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		g.insert_edge("a", "e", 4);
		g.insert_edge("c", "a", 4);
		REQUIRE(g.connections("a") == std::vector<std::string>{"a", "b", "e"});
		auto const d = g;
		REQUIRE(d.connections("a") == std::vector<std::string>{"a", "b", "e"});
	}

	SECTION("check src is not existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "e"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		g.insert_edge("a", "e", 4);
		g.insert_edge("c", "a", 4);
		auto temp = std::vector<std::string>();
		REQUIRE_THROWS(temp = g.connections("p"),
		               "Cannot call gdwg::graph<N, E>::connections "
		               "if src doesn't exist in the graph");
		auto const d = g;
		REQUIRE_THROWS(temp = d.connections("p"),
		               "Cannot call gdwg::graph<N, E>::connections "
		               "if src doesn't exist in the graph");
	}
}
