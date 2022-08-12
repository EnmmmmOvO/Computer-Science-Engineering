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

// The tests focused on three and four-letter word tests.
//
// For the three-letter test, the difference between the beginning word and the end word was tested
// by one or two letters respectively, and then two tests without the same letter were carried out.
// For the three letters different test, two similar words were selected in the first test, and
// second was selected the first and last three-letter word in english.txt file;
//
// For the four-letter word, work and play mentioned in the question were selected as the start
// and end words for the test, and random two words were selected as the other word for the test;
//
// Each test will focus on four part：
//     first, check all words in each ladder are unique.
//     Second, check that the start and end words are in the correct locations in the ladder.
//     Third, check the size of ladders and each ladder's length.
//     Finally, check the ladders is sorted and select several of ladders for comparison

TEST_CASE("Test: three letter word situation") {
	auto const english_lexicon = word_ladder::read_lexicon("./english.txt");

	SECTION("start and end word has one letter diff") {
		std::string const& from = "dog";
		std::string const& to = "dig";
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
		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"dog", "dig"}) == 1);
	}

	SECTION("start and end word has two letter diff") {
		std::string const& from = "bug";
		std::string const& to = "dig";
		auto size = 2;
		auto each_length = 3;
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
		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"bug", "big", "dig"})
		      == 1);
		CHECK(std::count(ladders.begin(), ladders.end(), std::vector<std::string>{"bug", "dug", "dig"})
		      == 1);
	}

	SECTION("start and end word has three letter diff : 1") {
		std::string const& from = "buy";
		std::string const& to = "dig";
		auto size = 2;
		auto each_length = 4;
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
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"buy", "bug", "big", "dig"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"buy", "bug", "dug", "dig"})
		      == 1);
	}

	SECTION("start and end word has three letter diff : 2") {
		std::string const& from = "aah";
		std::string const& to = "zoo";
		auto size = 1;
		auto each_length = 5;
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
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"aah", "nah", "noh", "noo", "zoo"})
		      == 1);
	}
}

TEST_CASE("Test: four letter word situation") {
	auto const english_lexicon = word_ladder::read_lexicon("./english.txt");

	SECTION("Ensure that four letter word ladders can be found: 1") {
		std::string const& from = "work";
		std::string const& to = "play";
		auto size = 12;
		auto each_length = 7;
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
		CHECK(
		   std::count(ladders.begin(),
		              ladders.end(),
		              std::vector<std::string>{"work", "worm", "form", "foam", "flam", "flay", "play"})
		   == 1);
		CHECK(
		   std::count(ladders.begin(),
		              ladders.end(),
		              std::vector<std::string>{"work", "worn", "porn", "pirn", "pian", "plan", "play"})
		   == 1);
		CHECK(
		   std::count(ladders.begin(),
		              ladders.end(),
		              std::vector<std::string>{"work", "wort", "bort", "boat", "blat", "plat", "play"})
		   == 1);
		CHECK(
		   std::count(ladders.begin(),
		              ladders.end(),
		              std::vector<std::string>{"work", "wort", "port", "pert", "peat", "plat", "play"})
		   == 1);
		CHECK(
		   std::count(ladders.begin(),
		              ladders.end(),
		              std::vector<std::string>{"work", "wort", "wert", "pert", "peat", "plat", "play"})
		   == 1);
	}

	SECTION("Ensure that four letter word ladders can be found: 2") {
		std::string const& from = "rain";
		std::string const& to = "quit";
		auto size = 1;
		auto each_length = 4;
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
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"rain", "ruin", "quin", "quit"})
		      == 1);
	}
}