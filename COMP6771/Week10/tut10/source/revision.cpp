#include <iostream>
#include <utility>

auto e(const int& i, int j, int k) -> void {
	std::cout << "1 ";
}

auto e(int& i, int j, int k) -> void {
	std::cout << "2 ";
}

template <typename A, typename B, typename C>
auto f(A&& a, B &&b, C&& c) -> void {
	e(std::forward<A>(a), std::forward<B>(b), std::forward<C>(c));
}

int k{1};

auto g() -> int {
	return k;
}

auto main() -> int {
	f(1,2,3);
	int i{1};
	f(i,2,3);
	const int &j = i;
	f(j,2,3);
	f(g(),2,3);
}

