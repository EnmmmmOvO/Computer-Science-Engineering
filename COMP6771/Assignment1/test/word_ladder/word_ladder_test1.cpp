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

#include <string>
#include <vector>

#include <catch2/catch.hpp>

// This part of the test mainly tests some unexpected situations of input, including that the
// length of the start and end is different, the words of the start, the upper situation
// and end are no longer in lexicon, and the words of the start and end are the same as the words
// of the end. All of them return an empty vector, so the size == 0
TEST_CASE("Ensure that application returns empty ladders if assignment "
          "assumptions are not complied with") {
	auto const english_lexicon = word_ladder::read_lexicon("./english.txt");

	SECTION("The length of Start word and End word is not equal") {
		auto ladders = word_ladder::generate("works", "play", english_lexicon);
		CHECK(std::size(ladders) == 0);
	}

	SECTION("Start word and End word is the same") {
		auto ladders = word_ladder::generate("work", "work", english_lexicon);
		CHECK(std::size(ladders) == 0);
	}

	SECTION("Start word and End word is include upper letter") {
		auto ladders = word_ladder::generate("Work", "Play", english_lexicon);
		CHECK(std::size(ladders) == 0);
	}

	SECTION("Start word not in lexicon") {
		auto ladders = word_ladder::generate("abcd", "play", english_lexicon);
		CHECK(std::size(ladders) == 0);
	}

	SECTION("End word not in lexicon") {
		auto ladders = word_ladder::generate("work", "abcd", english_lexicon);
		CHECK(std::size(ladders) == 0);
	}
}
