#include "comp6771/word_ladder.hpp"

// Please note: it's not good practice to test your code via a main function that does
//  printing. Instead, you should be using your test folder. This file should only really
//  be used for more "primitive" debugging as we know that working solely with test
//  frameworks might be overwhelming for some.
auto main() -> int {
	auto const english_lexicon = word_ladder::read_lexicon("../test/word_ladder/english.txt");
	auto const ladders = word_ladder::generate("fly", "sky", english_lexicon);
}