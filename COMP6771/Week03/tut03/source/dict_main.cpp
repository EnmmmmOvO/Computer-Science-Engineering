#include "dict.h"
#include <fstream>
#include <iostream>

auto main() -> int{
	auto file = std::fstream{"/Users/enmmmmovo/Documents/Study/COMP6771-gitlab/tut03/test/words"};
	auto const words = std::vector<std::string>{std::istream_iterator<std::string>(file), std::istream_iterator<std::string>()};
	std::copy_if(std::istream_iterator<std::string>(std::cin), std::istream_iterator<std::string>(),
	   std::ostream_iterator<std::string>(std::cout), [&] ());
}

