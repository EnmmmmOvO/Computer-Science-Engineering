#include <unordered_map>

#include "is_permutation.hpp"

// Similarly to `all_unique`, the idea behind this tute question is to get you to play with
// `std::unordered_map` in case you decide it's necessary for Word Ladder. There are other, even
// solutions out there, so if you discovered one --- which is great! --- please spend some time
// tinkering with `std::unordered_map` to get a better handle on its usage.
auto count_letters(std::string const& x) -> std::unordered_map<char, int> {
	auto dictionary = std::unordered_map<char, int>();

	for (auto const letter : x) {
		// `std::unordered_map::find` looks for a key, and returns an iterator to the key/value pair
		// entry in the map. It's different to `ranges::find` --- and better suited --- since it is
		// specialised for hash-table lookups, whereas `ranges::find` is suited for linear searches.
		// With a few exceptions, if there's a member function for a container and a `ranges::`
		// function with the same name, the member function is usually better-suted than the
		// `ranges::` function.
		//
		// At this point in the course, the exceptions include: `ranges::begin`, `ranges::end`, and
		// `ranges::swap`, all of which can be used *interchangably* with the member counterpart.
		// We'll expand on this a lot more in Week 7 (iterator week).
		auto result = dictionary.find(letter);

		// Since `dictionary.find` might have returned the sentinel value to indicate 'not found', we
		// need to check whether or not we actually found something before using it. If we try to use
		// something that doesn't exist, we've got a logic error. Exercise: try removing the whole
		// if-statement (lines 28-33) and see what happens in both Debug and Release modes. You'll
		// find that the program is wrong in both cases, but what happens might be different.
		if (result == dictionary.cend()) {
			// If there wasn't an entry, then we'd better add it, then move on to the next character in
			// the string.
			dictionary.emplace(letter, 1);
			continue;
		}

		// Here we increment the value part of our key/value pair. We're not allowed to modify the key
		// (Exercise: what happens if you change `second` to `first` and actually try modifying it?).
		// `result->second` is a shorthand way of saying `(*exercise).second`. We will cover how this
		// works partly in Week 3 and then follow up on it in Week 7 (iterator week).
		++result->second;
	}

	return dictionary;
}

auto is_permutation(std::string const& x, std::string const& y) -> bool {
	return count_letters(x) == count_letters(y);
}
