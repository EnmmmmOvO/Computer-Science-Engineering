#include <iostream>

template <typename T>
T max(T a, T b) {
	return a < b ? b : a;
}

auto main() -> int {
	auto result = 7;
	std::cout << max(1, 2) << "\n";
	std::cout << max(1.1, 2.2) << "\n";
	std::cout << max(1.0, 2.0) << "\n";
	std::cout << max('a', 'z') << "\n";
	std::cout << max(7, result) << "\n";
	std::cout << max("cat", "dog") << "\n";
}