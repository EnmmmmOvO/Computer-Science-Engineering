#ifndef COMP6771_ROPE_HPP
#define COMP6771_ROPE_HPP

#include <string>
#include <utility>
#include <vector>

class rope {
public:
	explicit rope(std::vector<std::string> rope)
	: rope_{std::move(rope)} {}

	class iterator {
	public:
		// TODO(tutorial): add iterator members types to model std::forward_iterator

		// TODO(tutorial): add member functions to model std::forward_iterator
	private:
		// TODO(tutorial): What data members should we put here?
	};

	// TODO(tutorial): add member functions here to make this a range.

private:
	std::vector<std::string> rope_;
};

#endif // COMP6771_ROPE_HPP
