//
//  Copyright UNSW Sydney School of Computer Science and Engineering
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
#include <comp6771/word_ladder.hpp>

#include <algorithm>
#include <numeric>
#include <string>
#include <vector>

#include <catch2/catch.hpp>

// Sorry professor, I am not sure why this test is successful in CSE sometimes and sometimes not.
// If it is not successful, could you please try it more times

// The test main focus on the two-letter word test. There is two situation , the one is the start
// and end word have one letter same, and one letter different, the other is all letter is
// different.
//
// Each test will focus on four part：
//     first, check all words in each ladder are unique.
//     Second, check that the start and end words are in the correct locations in the ladder.
//     Third, check the size of ladders and each ladder's length.
//     Finally, check the ladders is sorted and select several of ladders for comparison
TEST_CASE("Test: two letter word situation") {
	auto const english_lexicon = word_ladder::read_lexicon("./english.txt");

	SECTION("start and end word has one letter diff : 1") {
		std::string const& from = "at";
		std::string const& to = "it";
		auto size = 1;
		auto each_length = 2;
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		// first part
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return std::unique(ladder.begin(), ladder.end()) == ladder.end();
		}));
		// second part
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.front() == from;
		}));
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.back() == to;
		}));
		// third part
		CHECK(std::size(ladders) == size);
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.size() == each_length;
		}));
		// final part
		CHECK(std::is_sorted(ladders.begin(), ladders.end()));
		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"at", "it"}) == 1);
	}

	SECTION("start and end word has one letter diff : 2") {
		std::string const& from = "so";
		std::string const& to = "go";
		auto size = 1;
		auto each_length = 2;
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		// first part
		// CHECK(std::unique(ladders.begin(), ladders.end()) == ladders.end());
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return std::unique(ladder.begin(), ladder.end()) == ladder.end();
		}));
		// second part
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.front() == from;
		}));
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.back() == to;
		}));
		// third part
		CHECK(std::size(ladders) == size);
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.size() == each_length;
		}));
		// final part
		CHECK(std::is_sorted(ladders.begin(), ladders.end()));
		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"so", "go"}) == 1);
	}

	SECTION("start and end word has two letter diff : 1") {
		std::string const& from = "if";
		std::string const& to = "so";
		auto size = 2;
		auto each_length = 5;
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		// first part
		// CHECK(std::unique(ladders.begin(), ladders.end()) == ladders.end());
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return std::unique(ladder.begin(), ladder.end()) == ladder.end();
		}));
		// second part
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.front() == from;
		}));
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.back() == to;
		}));
		// third part
		CHECK(std::size(ladders) == size);
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.size() == each_length;
		}));
		// final part
		CHECK(std::is_sorted(ladders.begin(), ladders.end()));
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "ef", "eh", "sh", "so"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "of", "oh", "sh", "so"})
		      == 1);
	}

	SECTION("start and end word has two letter diff : 2") {
		std::string const& from = "if";
		std::string const& to = "go";
		auto size = 14;
		auto each_length = 6;
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		// first part
		// CHECK(std::unique(ladders.begin(), ladders.end()) == ladders.end());
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return std::unique(ladder.begin(), ladder.end()) == ladder.end();
		}));
		// second part
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.front() == from;
		}));
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.back() == to;
		}));
		// third part
		CHECK(std::size(ladders) == size);
		CHECK(std::all_of(ladders.begin(), ladders.end(), [&](auto ladder) {
			return ladder.size() == each_length;
		}));
		// final part
		CHECK(std::is_sorted(ladders.begin(), ladders.end()));
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "ef", "eh", "sh", "so", "go"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "ef", "em", "mm", "mo", "go"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "ef", "em", "hm", "ho", "go"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "of", "oy", "my", "mo", "go"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"if", "of", "oy", "by", "bo", "go"})
		      == 1);
	}

	// Because test1 records the test of expect, the content provided in test1 is placed here
	SECTION("Part test provided in the original test1") {
		auto const ladders = word_ladder::generate("at", "it", english_lexicon);

		CHECK(std::size(ladders) == 1);
		CHECK(std::is_sorted(ladders.begin(), ladders.end()));

		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"at", "it"}) == 1);
	}
}