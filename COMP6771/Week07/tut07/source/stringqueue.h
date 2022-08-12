#ifndef STRINGQUEUE_H_
#define STRINGQUEUE_H_

#include <string>
#include <memory>

class stringqueue {
public:
	stringqueue(int size) : size_curr_{0} size_max_{size}, queue_{std::make_unique<std::string[]>(size)} {}
	auto enque(std::string s) -> void;
	auto deque() -> std::string;
	auto size() const -> int;
private:
	int size_curr_;
	int size_max_;
	std::unique_ptr<std::string[]> queue_;
}

#endif  // STRINGQUEUE_H_