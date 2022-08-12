#include "gdwg/graph.hpp"

#include <catch2/catch.hpp>

// In this section, I primarily test the modifiers section.
//
// For insert_node, replace_edge, erase_node, clear function, I try all situation which follow the
// topic, if the return type is bool, check the status; if existed throw, require_throw and check
// the sentence is matching
//
// For replace_edge and merge_replace_edge function, except the normal test to satisfy the topic,
// I also check when replace the node, the edge and node set will also change with the new node
// information.
//
// For erase_node, the first situation test follow by the topic like above, the second and third
// situation about iterator, I test the iterator is any one, the last one and is g.end()' situations
// To cover all the possibility, I also check the return it and confirm them return true iterator.

TEST_CASE("Test insert_node function") {
	SECTION("Add node into an empty graph") {
		auto g = gdwg::graph<std::string, int>();
		REQUIRE(g.empty());
		REQUIRE(g.insert_node("b"));
		REQUIRE_FALSE(g.empty());
		REQUIRE(g.insert_node("a"));
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b"});
	}

	SECTION("Add node into no empty graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b"});
		REQUIRE(g.insert_node("c"));
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b", "c"});
	}

	SECTION("Add a node which the node information had existed in graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b"});
		REQUIRE_FALSE(g.insert_node("a"));
		REQUIRE(g.nodes() == std::vector<std::string>{"a", "b"});
	}
}

TEST_CASE("Test insert_edge function") {
	SECTION("Add edge into graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("a", "b", 1);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  b | 1\n"
		           ")\n"
		           "b (\n"
		           ")\n");
	}

	SECTION("Add edge with same src and dst which have different weight into graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.insert_edge("a", "b", 1));
		REQUIRE(g.insert_edge("a", "b", 2));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           ")\n"
		           "b (\n"
		           ")\n");
	}

	SECTION("Add edge with same src and dst which have same weight into graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.insert_edge("a", "b", 1));
		REQUIRE_FALSE(g.insert_edge("a", "b", 1));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  b | 1\n"
		           ")\n"
		           "b (\n"
		           ")\n");
	}

	SECTION("Add an edge which src or dst is not exist") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE_THROWS(g.insert_edge("z", "b", 1),
		               "Cannot call gdwg::graph<N, E>::"
		               "insert_edge when either src or dst node does not "
		               "exist");
		REQUIRE_THROWS(g.insert_edge("a", "c", 1),
		               "Cannot call gdwg::graph<N, E>::"
		               "insert_edge when either src or dst node does not "
		               "exist");
		REQUIRE_THROWS(g.insert_edge("1", "c", 1),
		               "Cannot call gdwg::graph<N, E>::"
		               "insert_edge when either src or dst node does not "
		               "exist");
	}
}

TEST_CASE("Test replace_node function") {
	SECTION("replace the graph only have node") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.replace_node("a", "c"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(g.nodes() == std::vector<std::string>{"b", "c"});
		REQUIRE(string_stream.str()
		        == "b (\n"
		           ")\n"
		           "c (\n"
		           ")\n");
	}

	SECTION("replace the graph which have node and edge") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE(g.replace_node("a", "c"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "b (\n"
		           "  c | 1\n"
		           ")\n"
		           "c (\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           "  c | 3\n"
		           "  c | 4\n"
		           ")\n");
	}

	SECTION("replace the node which is existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE_FALSE(g.replace_node("a", "b"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  a | 3\n"
		           "  a | 4\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           ")\n"
		           "b (\n"
		           "  a | 1\n"
		           ")\n");
	}

	SECTION("replace the old node or new node which is not existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE_THROWS(g.replace_node("c", "b"),
		               "Cannot call gdwg::graph<N, E>::"
		               "replace_node on a node that doesn't exist");
		REQUIRE_THROWS(g.replace_node("c", "d"),
		               "Cannot call gdwg::graph<N, E>::"
		               "replace_node on a node that doesn't exist");
	}
}

TEST_CASE("Test merge_replace_node function") {
	SECTION("merge the graph only have node") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE_NOTHROW(g.merge_replace_node("a", "b"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(g.nodes() == std::vector<std::string>{"b"});
		REQUIRE(string_stream.str()
		        == "b (\n"
		           ")\n");
	}

	SECTION("merge the graph which have node and edge") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		g.merge_replace_node("a", "c");
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "b (\n"
		           "  c | 1\n"
		           ")\n"
		           "c (\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           "  c | 3\n"
		           "  c | 4\n"
		           ")\n");
	}

	SECTION("merge the graph which have node and edge") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "c", 2);
		g.insert_edge("a", "d", 3);
		g.insert_edge("b", "b", 1);
		g.merge_replace_node("a", "b");
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "b (\n"
		           "  b | 1\n"
		           "  c | 2\n"
		           "  d | 3\n"
		           ")\n"
		           "c (\n"
		           ")\n"
		           "d (\n"
		           ")\n");
	}

	SECTION("merge the old node or new node which is not existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE_THROWS(g.merge_replace_node("a", "f"),
		               "Cannot call gdwg::"
		               "graph<N, E>::merge_replace_node on old or "
		               "new data if they don't exist in the graph");
		REQUIRE_THROWS(g.merge_replace_node("d", "a"),
		               "Cannot call gdwg::"
		               "graph<N, E>::merge_replace_node on old or "
		               "new data if they don't exist in the graph");
	}
}

TEST_CASE("Test erase node function") {
	SECTION("erase the graph only have node") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		REQUIRE(g.erase_node("a"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(g.nodes() == std::vector<std::string>{"b"});
		REQUIRE(string_stream.str()
		        == "b (\n"
		           ")\n");
	}

	SECTION("erase the graph which have node and edge") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE(g.erase_node("a"));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "b (\n"
		           ")\n"
		           "c (\n"
		           ")\n");
	}

	SECTION("erase the not existed node") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c", "d"};
		REQUIRE_FALSE(g.erase_node("f"));
		REQUIRE_FALSE(g.erase_node("g"));
	}
}

TEST_CASE("Test erase edge function") {
	SECTION("erase the edge with src, dst, weight") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE(g.erase_edge("b", "a", 1));
		REQUIRE(g.erase_edge("a", "a", 3));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  a | 4\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           ")\n"
		           "b (\n"
		           ")\n"
		           "c (\n"
		           ")\n");
	}

	SECTION("erase the weight is not existed") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		REQUIRE_FALSE(g.erase_edge("b", "a", 10));
		REQUIRE_FALSE(g.erase_edge("a", "a", 10));
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  a | 3\n"
		           "  a | 4\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           ")\n"
		           "b (\n"
		           "  a | 1\n"
		           ")\n"
		           "c (\n"
		           ")\n");
	}

	SECTION("erase the src and dst is not connected.") {
		auto g = gdwg::graph<std::string, int>{"a", "b", "c"};
		REQUIRE_FALSE(g.erase_edge("b", "a", 10));
		REQUIRE_FALSE(g.erase_edge("a", "a", 10));
	}

	SECTION("erase the src and dst is not existed.") {
		auto g = gdwg::graph<std::string, int>{"a"};
		REQUIRE_THROWS(g.erase_edge("b", "a", 10),
		               "Cannot call gdwg::graph<N, E>::"
		               "erase_edge on src or dst if they don't exist "
		               "in the graph");
		REQUIRE_THROWS(g.erase_edge("c", "a", 10),
		               "Cannot call gdwg::graph<N, E>::"
		               "erase_edge on src or dst if they don't exist "
		               "in the graph");
	}

	SECTION("erase the single iterator and the iterator is not the last one") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		auto it = g.begin();
		++it;
		it = g.erase_edge(it);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  a | 3\n"
		           "  b | 1\n"
		           "  b | 2\n"
		           ")\n"
		           "b (\n"
		           "  a | 1\n"
		           ")\n");
		auto iterator_position = *it;
		REQUIRE(iterator_position.from == "a");
		REQUIRE(iterator_position.to == "b");
		REQUIRE(iterator_position.weight == 1);
	}

	SECTION("erase the single iterator and the iterator is the last one") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		auto it = g.begin();
		++it;
		it = g.erase_edge(it);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  b | 1\n"
		           ")\n"
		           "b (\n"
		           ")\n");
		REQUIRE(it == g.end());
	}

	SECTION("erase the single iterator and the iterator is end()") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		auto it = g.begin();
		++it;
		it = g.erase_edge(it);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           ")\n"
		           "b (\n"
		           "  a | 1\n"
		           ")\n");
		REQUIRE(it == g.end());
	}

	SECTION("erase the range iterator, end iterator is not g.end()") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		auto it = g.begin();
		++it;
		auto it_end = g.begin();
		++it_end;
		++it_end;
		++it_end;
		++it_end;
		it = g.erase_edge(it, it_end);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           "  a | 3\n"
		           ")\n"
		           "b (\n"
		           "  a | 1\n"
		           ")\n");
		REQUIRE(it == it_end);
	}

	SECTION("erase the range iterator, end iterator is g.end()") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		auto it = g.begin();
		auto it_end = g.end();
		it = g.erase_edge(it, it_end);
		std::stringstream string_stream;
		string_stream << g;
		REQUIRE(string_stream.str()
		        == "a (\n"
		           ")\n"
		           "b (\n"
		           ")\n");
		REQUIRE(it == it_end);
	}
}

TEST_CASE("Test clear function") {
	SECTION("clear empty graph") {
		auto g = gdwg::graph<std::string, int>();
		g.clear();
		REQUIRE(g.empty());
	}

	SECTION("clear normal graph") {
		auto g = gdwg::graph<std::string, int>{"a", "b"};
		g.insert_edge("b", "a", 1);
		g.insert_edge("a", "b", 1);
		g.insert_edge("a", "b", 2);
		g.insert_edge("a", "a", 3);
		g.insert_edge("a", "a", 4);
		g.clear();
		REQUIRE(g.empty());
	}
}
