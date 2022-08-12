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

// This test focuses on multi-letter words, measuring 5, 9, 12, 15 letters word,
// and also include no solution situation.
//
// Each test will focus on four part：
//     first, check all words in each ladder are unique.
//     Second, check that the start and end words are in the correct locations in the ladder.
//     Third, check the size of ladders and each ladder's length.
//     Finally, check the ladders is sorted and select several of ladders for comparison
// If no solution, check the ladders is empty;
TEST_CASE("Test: more letters word situation") {
	auto const english_lexicon = word_ladder::read_lexicon("./english.txt");

	SECTION("Ensure that five letter word ladders can be found : short ladder") {
		std::string const& from = "pelon";
		std::string const& to = "macon";
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
		                 std::vector<std::string>{"pelon", "melon", "meson", "mason", "macon"})
		      == 1);
	}

	SECTION("Ensure that five letter word ladders can be found : long ladder") {
		std::string const& from = "print";
		std::string const& to = "watch";
		auto size = 1;
		auto each_length = 9;
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
		                 std::vector<std::string>{"print",
		                                          "paint",
		                                          "pains",
		                                          "pairs",
		                                          "lairs",
		                                          "laics",
		                                          "laich",
		                                          "latch",
		                                          "watch"})
		      == 1);
	}

	SECTION("five letter word ladders: no solution") {
		std::string const& from = "zombi";
		std::string const& to = "large";
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		CHECK(ladders.empty());
	}

	SECTION("Ensure that five letter word ladders can be found : 2") {
		std::string const& from = "decanting";
		std::string const& to = "derailing";
		auto size = 6;
		auto each_length = 18;
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
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "reletting",
		                                          "relenting",
		                                          "relending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "remailing",
		                                          "retailing",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "reletting",
		                                          "relenting",
		                                          "relending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "retaining",
		                                          "detaining",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "reletting",
		                                          "relenting",
		                                          "relending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "retaining",
		                                          "retailing",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "resetting",
		                                          "resenting",
		                                          "resending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "remailing",
		                                          "retailing",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "resetting",
		                                          "resenting",
		                                          "resending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "retaining",
		                                          "detaining",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"decanting",
		                                          "recanting",
		                                          "recasting",
		                                          "retasting",
		                                          "retesting",
		                                          "revesting",
		                                          "revetting",
		                                          "resetting",
		                                          "resenting",
		                                          "resending",
		                                          "remending",
		                                          "remanding",
		                                          "remanning",
		                                          "remaining",
		                                          "retaining",
		                                          "retailing",
		                                          "detailing",
		                                          "derailing"})
		      == 1);
	}

	SECTION("nine letter word ladders: no solution") {
		std::string const& from = "zygotenes";
		std::string const& to = "zirconias";
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		CHECK(ladders.empty());
	}

	SECTION("Ensure that twelve letter word ladders can be found") {
		std::string const& from = "romanticized";
		std::string const& to = "romanticizes";
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
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"romanticized", "romanticizes"})
		      == 1);
	}

	SECTION("twelve letter word ladders: no solution") {
		std::string const& from = "romanticized";
		std::string const& to = "zoologically";
		auto size = 0;
		auto each_length = 0;
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		CHECK(ladders.empty());
	}

	SECTION("Ensure that fifteen letter word ladders can be found") {
		std::string const& from = "unexceptionably";
		std::string const& to = "unexceptionable";
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
		CHECK(std::count(ladders.begin(),
		                 ladders.end(),
		                 std::vector<std::string>{"unexceptionably", "unexceptionable"})
		      == 1);
	}

	SECTION("fifteen letter word ladders: no solution") {
		std::string const& from = "sensationalized";
		std::string const& to = "traditionalisms";
		auto const ladders = word_ladder::generate(from, to, english_lexicon);

		CHECK(ladders.empty());
	}
}
