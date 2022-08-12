#include <fstream>
#include <iomanip>
#include <iostream>

#include <cmath>
#include <q1/q1.hpp>

namespace q1 {


	auto split(auto sentence) -> std::vector<std::string> {
		auto return_list = std::vector<std::string>();
		char* sentence_str = new char[sentence.size() + 1];
		std::strcpy(sentence_str, sentence.c_str());

		auto *temp = std::strtok(sentence_str, " ");
		while (temp != nullptr) {
			std::string temp_string = temp;
			return_list.push_back(temp_string);
			temp = std::strtok(nullptr, " ");
		}
		return return_list;
	}

	auto asmd(auto& operator_, auto& stack, auto& output) -> void {
		auto x = stack.front();
		stack.erase(stack.begin());
		auto y = stack.front();
		stack.erase(stack.begin());
		auto check_double = x.find('.') != std::string::npos || y.find('.') != std::string::npos;
		if (check_double) {
			auto x_ = stod(x);
			auto y_ = stod(y);
			if (operator_ == "add") {
				stack.push_back(x);
				output.push_back(x + " + " + y + " = " + std::to_string((x_ + y_)));
			} else if (operator_ == "sub") {
				stack.push_back(std::to_string(x_ - y_));
				output.push_back(x + " - " + y + " = " + std::to_string(x_ - y_));
			}
			else if (operator_ == "mult") {
				stack.push_back(std::to_string(x_ * y_));
				output.push_back(x + " - " + y + " = " + std::to_string(x_ * y_));
			}
			else if (operator_ == "sub") {
				auto temp = x_ / y_;
				if (temp - (int)temp == 0) {
					stack.push_back(std::to_string(static_cast<int>(temp)));
					output.push_back(x + " * " + y + " = " + std::to_string(static_cast<int>(temp)));
				}
				else {
					stack.push_back(std::to_string(temp));
					output.push_back(x + " * " + y + " = " + std::to_string(temp));
				}
			}
		} else {
			auto x_ = stoi(x);
			auto y_ = stoi(y);
			if (operator_ == "add") {
				stack.push_back(std::to_string(x_ + y_));
				output.push_back(x + " + " + y + " = " + std::to_string(x_ + y_));
			}
			else if (operator_ == "sub") {
				stack.push_back(std::to_string(x_ - y_));
				output.push_back(x + " - " + y + " = " + std::to_string(x_ - y_));
			}
			else if (operator_ == "mult") {
				stack.push_back(std::to_string(x_ * y_));
				output.push_back(x + " - " + y + " = " + std::to_string(x_ * y_));
			}
			else if (operator_ == "sub") {
				auto temp = x_ / y_;
				if (temp - (int)temp == 0) {
					stack.push_back(std::to_string(static_cast<int>(temp)));
					output.push_back(x + " * " + y + " = " + std::to_string(static_cast<int>(temp)));
				}
				else {
					stack.push_back(std::to_string(temp));
					output.push_back(x + " * " + y + " = " + std::to_string(temp));
				}
			}
		}
	}

	auto run_calculator(std::vector<std::string> const& input) -> std::vector<std::string> const {
		auto output = std::vector<std::string>{};
		auto stack = std::vector<std::string>();
		auto check_repeat = int{0};
		auto action = std::vector<std::string>{};

		std::for_each(input.cbegin(), input.cend(), [&] (auto const& sentence) {
			auto list = split(sentence);
			if (check_repeat == 0) {
				switch (list.size()) {
				case 3: {
					stack.insert(stack.begin(), list[0]);
					stack.insert(stack.begin(), list[1]);
					asmd(list[2], stack, output);
					break;
				}
				case 2: {
					if (list[1] == "add" || list[1] == "sub" || list[1] == "mult" || list[1] == "div") {
						stack.insert(stack.begin(), list[0]);
						asmd(list[1], stack, output);
					} else if (list[1] == "repeat") {
						check_repeat = stoi(list[0]);
					} else if (list[1] == "reverse") {
						auto temp = std::vector<std::string>{};
						for (int loop = stoi(list[0]); loop > 0; loop --) {
							temp.push_back(stack.front());
							stack.erase(stack.begin());
						}
						std::for_each(temp.rbegin(), temp.rend(), [&] (auto sentence) {
							stack.insert(stack.begin(), sentence);
						});
					}
					break ;
				}
				case 1: {
					if (list[0] == "add" || list[0] == "sub" || list[0] == "mult"
					    || list[0] == "div")
					{
						asmd(list[0], stack, output);
					} else if (list[0] == "pop") {
						stack.erase(stack.begin());
					} else if (list[0] == "sqrt") {
						auto x = stack.front();
						stack.erase(stack.begin());
						stack.insert(stack.begin(), std::to_string(std::sqrt(stod(x))));
						output.push_back("sqrt " + x + " = " + std::to_string(std::sqrt(stod(x))));
					} else {
						stack.insert(stack.begin(), list[0]);
					}
					break;
				}
				}
			} else {
				if (list.size() == 1 && list[0] == "endrepeat") {
					for (; check_repeat > 0; check_repeat--)
						std::for_each(action.cbegin(), action.cend(), [&](auto const& sentence) {
							auto list = split(sentence);
							switch (list.size()) {
							case 3: {
								stack.insert(stack.begin(), list[0]);
								stack.insert(stack.begin(), list[1]);
								asmd(list[2], stack, output);
								break;
							}
							case 2: {
								if (list[1] == "add" || list[1] == "sub" || list[1] == "mult"
								    || list[1] == "div")
								{
									stack.insert(stack.begin(), list[0]);
									asmd(list[1], stack, output);
								} else if (list[1] == "reverse") {
									auto temp = std::vector<std::string>{};
									for (int loop = stoi(list[0]); loop > 0; loop --) {
										temp.push_back(stack.front());
										stack.erase(stack.begin());
									}
									std::for_each(temp.rbegin(), temp.rend(), [&] (auto sentence) {
										stack.insert(stack.begin(), sentence);
									});
								}
								break;
							}
							case 1: {
								if (list[0] == "add" || list[0] == "sub" || list[0] == "mult"
								    || list[0] == "div")
								{
									asmd(list[0], stack, output);
								} else if (list[0] == "sqrt") {
									auto x = stack.front();
									stack.erase(stack.begin());
									stack.insert(stack.begin(), std::to_string(std::sqrt(stod(x))));
									output.push_back("sqrt " + x + " = " + std::to_string(std::sqrt(stod(x))));
								} else {
									stack.insert(stack.begin(), list[0]);
								}
								break;
							}
							}
						});
					action.clear();
				} else {
					action.push_back(sentence);
				}
			}

		});

		return output;
	}
} // namespace q1
