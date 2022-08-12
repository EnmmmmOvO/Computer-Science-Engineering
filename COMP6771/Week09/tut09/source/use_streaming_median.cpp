#include <streaming_median.h>

#include <iostream>
#include <memory>
#include <string>
#include <vector>

auto main() -> int {
  auto string_sm = streaming_median<std::string>{};
  auto dogs = std::vector<std::string>{"samoyed", "shiba inu", "corgi"};
  std::for_each(dogs.begin(), dogs.end(), [&](auto const& s) { string_sm.add(s); });

  std::cout << "Median of strings: " << string_sm.median() << "\n";

  auto int_sm = streaming_median<int>{};
  auto ints = std::vector<int>{1, 2, 3, 4, 5};
  std::for_each(ints.begin(), ints.end(), [&](auto i) { int_sm.add(i); });

  std::cout << "Median of ints: " << int_sm.median() << "\n";

  // Uncomment the following after completing part 2.

  // auto double_sm = streaming_median<double>{};
  // auto doubles = std::vector<double>{1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0};
  // std::for_each(doubles.begin(), doubles.end(), [&](auto d) { double_sm.add(d); });

  // std::cout << "Median of doubles: " << double_sm.median() << "\n";
}