
#include <iostream>
#include <vector>

int main() {
	std::vector<int> temperatures{32, 34, 33, 28, 35, 28, 34};

	for (int i = temperatures.size() - 1; i >= 0; --i) {
		std::cout << temperatures.at(i) << " ";
	}
	std::cout << "\n";

	// Can't do it with for-range

	for (auto iter = temperatures.crbegin(); iter != temperatures.crend(); ++iter) {
		std::cout << *iter << " ";
	}
	std::cout << "\n";
}
