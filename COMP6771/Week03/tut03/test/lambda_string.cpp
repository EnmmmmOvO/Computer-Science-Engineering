#include <string>
#include <vector>

#include <catch2/catch.hpp>

TEST_CASE("Checks sort3(int&, int&, int&)") {
	std::vector<std::string> vec{"We", "love", "lambda", "functions"};

	// Sort it here

	auto const vowels = [] (char const& c) {return c == 'a' || c == 'e' || c == 'o' || c == 'i' || c == 'u';};

	std::sort(vec.begin(), vec.end(), [vowels] (std::string const& word1, std::string const& word2) {
		auto temp1 = std::count(word1.cbegin(), word1.cend(), 'a' | 'e' | 'o' | 'i' | 'u');
		auto temp2 = std::count(word2.cbegin(), word2.cend(), 'a' | 'e' | 'o' | 'i' | 'u');
		return temp1 != temp2 ? temp1 > temp2 : word1.length() - static_cast<std::string::size_type>(temp1) > word2.length() - static_cast<std::string::size_type>(temp2);
	});

	std::vector<std::string> correct_order{"functions", "lambda", "love", "We"};
	CHECK(correct_order == vec);
}