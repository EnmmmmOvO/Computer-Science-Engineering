#include <comp6771/rope.hpp>

#include <algorithm>
#include <iostream>
#include <iterator>
#include <numeric>
#include <vector>

int main() {
	auto const ropes = std::vector<rope>{
	   rope{{"a"}},
	   rope{{"abc"}},
	   rope{{"abc"}},
	   rope{{"abc", "def"}},
	   rope{{"abc", "", "def"}},
	   rope{{""}},
	   rope{{"", "abc", "def", ""}},
	};

	using namespace std::string_literals;
	std::transform(ropes.begin(), ropes.end(), std::ostream_iterator<std::string>(std::cout, "\n"), [](rope const& r) {
		return std::accumulate(r.begin(), r.end(), "Rope: \""s) + '"';
	});
}
