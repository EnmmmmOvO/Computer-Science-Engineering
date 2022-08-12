#include <iostream>

struct foxtrot {
	~foxtrot() {
		std::cout << "~foxtrot()\n";
	}
};

struct yellow {
	~yellow() {
		std::cout << "~yellow()\n";
	}
};

class apple {
	foxtrot f;
public:
	~apple() {
		std::cout << "~apple()\n";
	}
};

class bingo : public apple {
	yellow y;
public:
	~bingo() {
		std::cout << "~bingo()\n";
	}
};

auto main() -> int {
	bingo b;
}
