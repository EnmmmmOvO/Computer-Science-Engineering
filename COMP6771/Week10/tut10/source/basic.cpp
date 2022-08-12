#include <iostream>

class animal {
public:
	animal() {
		std::cout << "animal\n";
	}
};

class amphibian {
public:
	amphibian() {
		std::cout << "amphibian\n";
	}
private:
	animal a1_;
};

class fish {
public:
	fish() {
		std::cout << "fish\n";
	}
private:
	animal a1_;
	amphibian a2_;
};

auto main() -> int {
	fish a3;
}
