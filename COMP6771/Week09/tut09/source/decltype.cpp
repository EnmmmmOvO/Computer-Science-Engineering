auto main() -> int {
	int i = 5;
	int& k = i;

	decltype(i) x;
	decltype(k) y;
	decltype(std::move(i)) z;
	decltype(4.2);
}