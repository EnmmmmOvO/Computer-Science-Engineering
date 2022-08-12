#include <array>
#include <cassert>
#include <vector>
#include <iostream>

enum class number_type {
  prime,
  composite,
};

auto generate_primes_lookup_table(int largest_value) -> std::vector<number_type> {
  assert(largest_value > 1);
  // all values initialized to "prime"
  auto result = std::vector<number_type>(static_cast<std::size_t>(largest_value));

  // 0 and 1 don't count, so we start at 2
  for (auto x = std::size_t{2}; x < result.size() / 2; ++x) {
    if (result[x] == number_type::prime) {
      for (auto y = x + x; y < result.size(); y += x) {
        result[y] = number_type::composite;
      }
    }
  }

  return result;
}

auto is_prime(int value) -> bool {
  // negative numbers, 0, and 1 are not prime
  if (value < 2) {
    return false;
  }

  // have a lookup table for fast checking of small primes
  static const auto lookup_table = generate_primes_lookup_table(10'000);
  if (value < 10'000) {
    return lookup_table[static_cast<std::size_t>(value)] == number_type::prime;
  }

  // larger values, we use trial by division
  // we can still use our lookup table to only check with relevant factors
  // (division is expensive!)
  for (auto i = 2; i < 10'000 and i < (value / 2); ++i) {
    if (lookup_table[static_cast<std::size_t>(i)] == number_type::prime) {
      if (value % i == 0) {
        return false;
      }
    }
  }

  // outside the range of our lookup table, let's just go for broke
  for (auto i = 10'000; i < (value / 2); ++i) {
    if (value % i == 0) {
      return false;
    }
  }

  // we have found no factors, therefore the number is prime
  return true;
}

auto main() -> int {
  std::cout << "Enter a number: ";
  auto i = 0;
  std::cin >> i;
  if (is_prime(i)) {
    std::cout << "The number is prime!\n";
  } else {
    std::cout << "The number is not prime.\n";
  }
}
