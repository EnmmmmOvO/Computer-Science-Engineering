#ifndef COMP6771_EUCLIDEAN_VECTOR_HPP
#define COMP6771_EUCLIDEAN_VECTOR_HPP

#include <cassert>
#include <iomanip>
#include <list>
#include <memory>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace comp6771 {
	class euclidean_vector_error : public std::runtime_error {
	public:
		explicit euclidean_vector_error(std::string const& what)
		: std::runtime_error(what) {}
	};

	class euclidean_vector {
	public:
		/* PART 1 - CONSTRUCTORS */
		euclidean_vector() noexcept;
		explicit euclidean_vector(int dimension) noexcept;
		euclidean_vector(int dimension, double value) noexcept;
		euclidean_vector(std::vector<double>::const_iterator const& begin,
		                 std::vector<double>::const_iterator const& end) noexcept;
		euclidean_vector(std::initializer_list<double> const& list) noexcept;
		euclidean_vector(euclidean_vector const& other) noexcept;
		euclidean_vector(euclidean_vector&& other) noexcept;

		/* PART 2 - DESTRUCTORS */
		~euclidean_vector();

		/* PART 3 - OPERATIONS */
		auto operator=(euclidean_vector const& rhs) noexcept -> euclidean_vector&;
		auto operator=(euclidean_vector&& other) noexcept -> euclidean_vector&;
		auto operator[](int index) noexcept -> double&;
		auto operator[](int index) const noexcept -> double;
		auto operator+() noexcept -> euclidean_vector;
		auto operator-() noexcept -> euclidean_vector;
		auto operator+=(euclidean_vector const& rhs) -> euclidean_vector;
		auto operator-=(euclidean_vector const& rhs) -> euclidean_vector;
		auto operator*=(double rhs) noexcept -> euclidean_vector;
		auto operator/=(double rhs) -> euclidean_vector;
		explicit operator std::vector<double>() noexcept;
		explicit operator std::list<double>() noexcept;

		/* PART 4 - MEMBER FUNCTIONS */
		[[nodiscard]] auto at(int index) const -> double;
		[[nodiscard]] auto at(int index) -> double&;
		[[nodiscard]] auto dimensions() const noexcept -> int;

		/* PART 5 - FRIENDS */
		friend auto operator==(euclidean_vector const& lhs, euclidean_vector const& rhs) noexcept
		   -> bool;
		friend auto operator!=(euclidean_vector const& lhs, euclidean_vector const& rhs) noexcept
		   -> bool;
		friend auto operator+(euclidean_vector const& lhs, euclidean_vector const& rhs)
		   -> euclidean_vector;
		friend auto operator-(euclidean_vector const& lhs, euclidean_vector const& rhs)
		   -> euclidean_vector;
		friend auto operator*(euclidean_vector const& lhs, double rhs) noexcept -> euclidean_vector;
		friend auto operator*(double lhs, euclidean_vector const& rhs) noexcept -> euclidean_vector;
		friend auto operator/(euclidean_vector const& lhs, double rhs) -> euclidean_vector;
		friend auto operator<<(std::ostream& output, euclidean_vector const& vector) noexcept
		   -> std::ostream&;

		/* PART 6 - HELP UTILITY FUNCTIONS */
		[[nodiscard]] auto get_euclidean_norm() const noexcept -> double;
		[[nodiscard]] auto get_dot(euclidean_vector const& vector) const noexcept -> double;

		/* Test Help Function */
		[[nodiscard]] auto test_get_euclidean_norm() const noexcept -> double;

	private:
		// Record the size of the vector
		size_t dimension_{};
		// ass2 spec requires we use std::unique_ptr<double[]>
		// NOLINTNEXTLINE(modernize-avoid-c-arrays)
		std::unique_ptr<double[]> magnitude_;
		// euclidean norm's cache, before calculation, it is -1 because all of euclidean norm
		// must greater and equal than 0. It is set to mutable, allowing it to change values
		// when calling const functions
		double mutable euclidean_norm_ = -1;
	};

	/* PART 6 - UTILITY FUNCTIONS */
	auto euclidean_norm(euclidean_vector const& vector) noexcept -> double;
	auto unit(euclidean_vector const& vector) -> euclidean_vector;
	auto dot(euclidean_vector const& x, euclidean_vector const& y) -> double;
} // namespace comp6771

#endif // COMP6771_EUCLIDEAN_VECTOR_HPP
