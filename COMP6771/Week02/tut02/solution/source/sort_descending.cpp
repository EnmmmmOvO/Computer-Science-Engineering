#include <vector>

#include "sort_descending.hpp"

auto sort_descending(std::vector<std::string>& numbers) -> void {
	std::sort(numbers, std::greater{});
}
