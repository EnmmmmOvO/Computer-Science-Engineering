#include <iostream>

class banana {
public:
	virtual auto f() -> void {
		std::cout << "banana ";
	}
};

class door : public banana {
public:
	auto f() override -> void {
		std::cout << "door ";
	}
};

auto main() -> int {
	banana b;
	door d;
	b = d;
	banana& bref = b;
	door& dref = d;
	banana& dbref = d;
	b.f();
	d.f();
	bref.f();
	dref.f();
	dbref.f();
}
