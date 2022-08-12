
#include <comp6771/ladder.hpp>
#include <comp6771/word_ladder.hpp>

namespace word_ladder {
	[[nodiscard]] auto generate(std::string const& from,
	                            std::string const& to,
	                            std::unordered_set<std::string> const& lexicon)
	   -> std::vector<std::vector<std::string>> {
		// Check start and end word is equal
		if (from.length() != to.length() || from == to)
			return {};
		// create the ladder class
		ladder ladder(from, to, lexicon);
		return ladder.start();
	}

} // namespace word_ladder
