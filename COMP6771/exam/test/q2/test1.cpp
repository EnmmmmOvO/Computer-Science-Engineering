#include <catch2/catch.hpp>

#include <cstddef>
#include <q2/q2.hpp>

#include <cstdlib>

using namespace q2;

struct {
	bool alive;
	int an_int;
} mm{};
auto my_malloc(std::size_t) -> int* {
	auto ptr = &mm.an_int;
	mm.alive = true;
	return ptr;
}

auto my_free(int *&) {
	mm.alive = false;
}

TEST_CASE("rewriting unique_ptr<int>") {
	using unique_iptr = scope_guard<int *, my_malloc, my_free>;

	// won't compile straight away
	{
		auto ip = unique_iptr(4ul);
		CHECK(bool(ip));
	} // no resource leak!
	CHECK_FALSE(mm.alive);
}
