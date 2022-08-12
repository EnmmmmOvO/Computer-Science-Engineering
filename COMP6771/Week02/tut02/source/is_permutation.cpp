#include <string>
#include <unordered_map>

auto create_map(std::string const& word)-> std::unordered_map<char, int> {
	auto map = std::unordered_map<char, int>();
	for (auto const& key: word) {
		auto temp = map.find(key);
		if (temp == map.cend()) {
			map.emplace(key, 1);
			continue;
		}
		temp->second++;
	}
	return map;
}

auto is_permutation(std::string const& x, std::string const& y) -> bool {
	return create_map(x) == create_map(y);
}