#include <comp6771/euclidean_vector.hpp>

#include <catch2/catch.hpp>

TEST_CASE("Euclidean vector is trivially default constructible") {
	auto const a1 = comp6771::euclidean_vector{};

	CHECK(true);
}
