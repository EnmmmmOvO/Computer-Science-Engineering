#include <iostream>
#include <vector>

int main() {
	std::vector<int> temperatures{32, 34, 33, 28, 35, 28, 34};

	for (auto i = 0; i < temperatures.size(); ++i) {
		std::cout << temperatures.at(i) << " ";
	}
	std::cout << "\n";

	for (const auto& temp : temperatures) {
		std::cout << temp << " ";
	}
	std::cout << "\n";

	for (auto iter = temperatures.cbegin(); iter != temperatures.cend(); ++iter) {
		std::cout << *iter << " ";
	}
	std::cout << "\n";

	std::for_each(temperatures.cbegin(), temperatures.cend(), [&] (auto temp) {std::cout << temp << " ";});
	std::cout << "\n";
}