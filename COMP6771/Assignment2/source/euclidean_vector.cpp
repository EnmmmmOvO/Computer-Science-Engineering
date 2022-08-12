// Copyright (c) Christopher Di Bella.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
#include <comp6771/euclidean_vector.hpp>

// Helper function declaration
auto throw_size_error_sentence(size_t lhs, size_t rhs) -> std::string;
auto throw_out_of_range_error_sentence(int index) -> std::string;

namespace comp6771 {

	/* PART 1 - CONSTRUCTORS */

	// --- Default Constructor ---
	// A constructor that generates a euclidean vector with a dimension of 1 and magnitude of 0.0.
	euclidean_vector::euclidean_vector() noexcept
	: dimension_{1} {
		magnitude_ = std::make_unique<double[]>(dimension_);
	}

	// --- Single-argument Constructor ---
	// A constructor that takes the number of dimensions (as an int) but no magnitudes, sets the
	// magnitude in each dimension as 0.0.
	euclidean_vector::euclidean_vector(int dimension) noexcept
	: dimension_{static_cast<size_t>(dimension)} {
		magnitude_ = std::make_unique<double[]>(dimension_);
	}

	// --- Constructor ---
	// A constructor that takes the number of dimensions (as an int) and initialises the
	// magnitude in each dimension as the second argument (a double).
	euclidean_vector::euclidean_vector(int dimension, double value) noexcept
	: dimension_{static_cast<size_t>(dimension)} {
		this->magnitude_ = std::make_unique<double[]>(dimension_);
		std::fill(this->magnitude_.get(), this->magnitude_.get() + this->dimension_, value);
	}

	// A constructor (or constructors) that takes the start and end of an iterator to a
	// std:vector<double> and works out the required dimensions, and sets the
	// magnitude in each dimension according to the iterated values.
	euclidean_vector::euclidean_vector(std::vector<double>::const_iterator const& begin,
	                                   std::vector<double>::const_iterator const& end) noexcept {
		dimension_ = static_cast<size_t>(std::distance(begin, end));
		magnitude_ = std::make_unique<double[]>(dimension_);
		std::copy(begin, end, magnitude_.get());
	}

	// A constructor that takes an initialiser list of doubles to populate vector
	// magnitudes. You will have to do your own research to implement this one.
	euclidean_vector::euclidean_vector(std::initializer_list<double> const& list) noexcept
	: dimension_{list.size()} {
		magnitude_ = std::make_unique<double[]>(dimension_);
		std::copy(list.begin(), list.end(), magnitude_.get());
	}

	// --- Copy Constructor ---
	euclidean_vector::euclidean_vector(euclidean_vector const& other) noexcept
	: dimension_{other.dimension_} {
		magnitude_ = std::make_unique<double[]>(dimension_);
		std::copy(other.magnitude_.get(),
		          other.magnitude_.get() + other.dimension_,
		          this->magnitude_.get());
	}

	// --- Move Constructor ---
	euclidean_vector::euclidean_vector(euclidean_vector&& other) noexcept
	: dimension_{other.dimension_}
	, magnitude_{std::move(other.magnitude_)} {
		other.dimension_ = 0;
	}

	/* PART 2 - DESTRUCTORS */

	// You must explicitly declare the destructor as default.
	euclidean_vector::~euclidean_vector() {
		this->magnitude_.reset();
	}

	/* PART 3 - OPERATIONS */

	// --- Copy Assignment ---
	// A copy assignment operator overload
	auto euclidean_vector::operator=(euclidean_vector const& rhs) noexcept -> euclidean_vector& {
		*this = euclidean_vector(rhs);
		return *this;
	}

	// --- Move Assignment ---
	// A move assignment operator
	auto euclidean_vector::operator=(euclidean_vector&& other) noexcept -> euclidean_vector& {
		this->dimension_ = other.dimension_;
		this->magnitude_ = std::move(other.magnitude_);
		other.dimension_ = 0;
		return *this;
	}

	// --- Subscript ---
	// Allows to get and set the value in a given dimension of the Euclidean vector.
	auto euclidean_vector::operator[](int index) noexcept -> double& {
		assert(index >= 0 && static_cast<size_t>(index) < this->dimension_);
		return this->magnitude_[static_cast<size_t>(index)];
	}

	// Allows to get the value in a given dimension of the Euclidean vector when const declaration.
	auto euclidean_vector::operator[](int index) const noexcept -> double {
		assert(index >= 0 && static_cast<size_t>(index) < this->dimension_);
		return this->magnitude_[static_cast<size_t>(index)];
	}

	// --- Unary plus ---
	// Returns a copy of the current object.
	auto euclidean_vector::operator+() noexcept -> euclidean_vector {
		return *this;
	}

	// --- Negation ---
	// Returns a copy of the current object, where each scalar value has its sign negated.
	auto euclidean_vector::operator-() noexcept -> euclidean_vector {
		auto new_euclidean_vector = euclidean_vector(static_cast<int>(this->dimension_));
		std::transform(this->magnitude_.get(),
		               this->magnitude_.get() + this->dimension_,
		               new_euclidean_vector.magnitude_.get(),
		               std::negate<double>{});
		return new_euclidean_vector;
	}

	// --- Compound Addition ---
	// For adding vectors of the same dimension.
	auto euclidean_vector::operator+=(euclidean_vector const& rhs) -> euclidean_vector {
		if (this->dimension_ != rhs.dimension_) {
			throw euclidean_vector_error(throw_size_error_sentence(this->dimension_, rhs.dimension_));
		}
		std::transform(this->magnitude_.get(),
		               this->magnitude_.get() + this->dimension_,
		               rhs.magnitude_.get(),
		               this->magnitude_.get(),
		               std::plus<double>{});
		return *this;
	}

	// --- Compound Subtraction ---
	// For subtracting vectors of the same dimension.
	auto euclidean_vector::operator-=(euclidean_vector const& rhs) -> euclidean_vector {
		if (this->dimension_ != rhs.dimension_) {
			throw euclidean_vector_error(throw_size_error_sentence(this->dimension_, rhs.dimension_));
		}
		std::transform(this->magnitude_.get(),
		               this->magnitude_.get() + this->dimension_,
		               rhs.magnitude_.get(),
		               this->magnitude_.get(),
		               std::minus<double>{});
		return *this;
	}

	// --- Compound Multiplication ---
	// For scalar multiplication
	auto euclidean_vector::operator*=(double rhs) noexcept -> euclidean_vector {
		std::for_each (this->magnitude_.get(),
		               this->magnitude_.get() + this->dimension_,
		               [&](double& value) { value *= rhs; });
		return *this;
	}

	// --- Compound Division ---
	// For scalar division
	auto euclidean_vector::operator/=(double rhs) -> euclidean_vector {
		if (rhs == 0) {
			throw euclidean_vector_error("Invalid vector division by 0");
		}
		std::for_each (this->magnitude_.get(),
		               this->magnitude_.get() + this->dimension_,
		               [&](double& value) { value /= rhs; });
		return *this;
	}

	// --- Vector Type Conversion ---
	// Operators for type casting to a std::vector
	euclidean_vector::operator std::vector<double>() noexcept {
		auto new_vector = std::vector<double>();
		new_vector.insert(new_vector.cbegin(),
		                  this->magnitude_.get(),
		                  this->magnitude_.get() + this->dimension_);
		return new_vector;
	}

	// --- List Type Conversion ---
	// Operators for type casting to a std::list
	euclidean_vector::operator std::list<double>() noexcept {
		auto new_list = std::list<double>();
		new_list.insert(new_list.cbegin(),
		                this->magnitude_.get(),
		                this->magnitude_.get() + this->dimension_);
		return new_list;
	}

	/* PART 4 - MEMBER FUNCTIONS */

	// Returns the value of the magnitude in the dimension given as the function parameter
	auto euclidean_vector::at(int index) const -> double {
		if (index < 0 || static_cast<size_t>(index) >= dimension_) {
			throw euclidean_vector_error(throw_out_of_range_error_sentence(index));
		}
		return this->magnitude_[static_cast<size_t>(index)];
	}

	// Returns the reference of the magnitude in the dimension given as the function parameter
	auto euclidean_vector::at(int index) -> double& {
		if (index < 0 || static_cast<size_t>(index) >= dimension_) {
			throw euclidean_vector_error(throw_out_of_range_error_sentence(index));
		}
		return this->magnitude_[static_cast<size_t>(index)];
	}

	// Return the number of dimensions in a particular euclidean_vector
	auto euclidean_vector::dimensions() const noexcept -> int {
		return static_cast<int>(this->dimension_);
	}

	/* PART 5 - FRIENDS */

	// --- Equal ---
	// True if the two vectors are equal in the number of dimensions and the magnitude in each
	// dimension is equal.
	auto operator==(euclidean_vector const& lhs, euclidean_vector const& rhs) noexcept -> bool {
		if (lhs.dimension_ != rhs.dimension_)
			return false;
		return std::equal(lhs.magnitude_.get(),
		                  lhs.magnitude_.get() + lhs.dimension_,
		                  rhs.magnitude_.get(),
		                  rhs.magnitude_.get() + rhs.dimension_);
	}

	// --- Not Equal ---
	// True if the two vectors are not equal in the number of dimensions or the magnitude in any
	// dimension is not equal.
	auto operator!=(euclidean_vector const& lhs, euclidean_vector const& rhs) noexcept -> bool {
		if (lhs.dimension_ != rhs.dimension_)
			return true;
		return !std::equal(lhs.magnitude_.get(),
		                   lhs.magnitude_.get() + lhs.dimension_,
		                   rhs.magnitude_.get(),
		                   rhs.magnitude_.get() + rhs.dimension_);
	}

	// --- Addition ---
	// For adding vectors of the same dimension.
	auto operator+(euclidean_vector const& lhs, euclidean_vector const& rhs) -> euclidean_vector {
		if (lhs.dimension_ != rhs.dimension_) {
			throw euclidean_vector_error(throw_size_error_sentence(lhs.dimension_, rhs.dimension_));
		}
		auto new_euclidean_vector = euclidean_vector(lhs);
		new_euclidean_vector += rhs;
		return new_euclidean_vector;
	}

	// --- Subtraction ---
	// For substracting vectors of the same dimension.
	auto operator-(euclidean_vector const& lhs, euclidean_vector const& rhs) -> euclidean_vector {
		if (lhs.dimension_ != rhs.dimension_) {
			throw euclidean_vector_error(throw_size_error_sentence(lhs.dimension_, rhs.dimension_));
		}
		auto new_euclidean_vector = euclidean_vector(lhs);
		new_euclidean_vector -= rhs;
		return new_euclidean_vector;
	}

	// --- Multiply ---
	//	For scalar multiplication  (euclidean_vector * value)
	auto operator*(euclidean_vector const& lhs, double rhs) noexcept -> euclidean_vector {
		auto new_euclidean_vector = euclidean_vector(lhs);
		new_euclidean_vector *= rhs;
		return new_euclidean_vector;
	}

	//	For scalar multiplication  (value * euclidean_vector)
	auto operator*(double lhs, euclidean_vector const& rhs) noexcept -> euclidean_vector {
		return operator*(rhs, lhs);
	}

	// --- Divide ---
	// For scalar division
	auto operator/(euclidean_vector const& lhs, double rhs) -> euclidean_vector {
		if (rhs == 0) {
			throw euclidean_vector_error("Invalid vector division by 0");
		}
		auto new_euclidean_vector = euclidean_vector(lhs);
		new_euclidean_vector /= rhs;
		return new_euclidean_vector;
	}

	// --- Output Stream ---
	// Prints out the magnitude in each dimension of the Euclidean vector.
	// P.S To solve the problem that there will be many zeros after the decimal point when printing
	// directly, so it can be printed to 10 digits after the decimal point at most.
	auto operator<<(std::ostream& output, euclidean_vector const& vector) noexcept -> std::ostream& {
		output << "[";
		auto temp = size_t{0};
		std::for_each (vector.magnitude_.get(),
		               vector.magnitude_.get() + vector.dimension_,
		               [&](double const& value) {
			               output << value;
			               temp++;
			               if (temp != vector.dimension_) {
				               output << std::setprecision(10) << " ";
			               }
		               });
		output << "]";
		return output;
	}

	/* PART 6 - UTILITY FUNCTIONS */

	// Returns the Euclidean norm of the vector as a double. The Euclidean norm is the
	// square root of the sum of the squares of the magnitudes in each dimension.
	auto euclidean_norm(euclidean_vector const& vector) noexcept -> double {
		return vector.get_euclidean_norm();
	}

	// Help Function to Euclidean norm.
	auto euclidean_vector::get_euclidean_norm() const noexcept -> double {
		this->euclidean_norm_ =
		   this->euclidean_norm_ == -1 ? static_cast<double>(sqrt(
		      std::accumulate(this->magnitude_.get(),
		                      this->magnitude_.get() + this->dimension_,
		                      double{0.0},
		                      [](double sum, double const& value) { return sum + value * value; })))
		                               : this->euclidean_norm_;
		return this->euclidean_norm_;
	}

	// Returns a Euclidean vector that is the unit vector of vector. The magnitude for each
	// dimension in the unit vector is the original vector's magnitude divided by the Euclidean norm.
	auto unit(euclidean_vector const& vector) -> euclidean_vector {
		if (vector.dimensions() == 0) {
			throw euclidean_vector_error("euclidean_vector with no dimensions does not "
			                             "have a unit vector");
		}
		auto euclidean_norm = vector.get_euclidean_norm();
		if (euclidean_norm == 0) {
			throw euclidean_vector_error("euclidean_vector with zero euclidean normal "
			                             "does not have a unit vector");
		}
		return vector / euclidean_norm;
	}

	// Computes the dot product of x * y; returns a double.
	auto dot(euclidean_vector const& vector1, euclidean_vector const& vector2) -> double {
		if (vector1.dimensions() != vector2.dimensions()) {
			throw euclidean_vector_error(
			   throw_size_error_sentence(static_cast<size_t>(vector1.dimensions()),
			                             static_cast<size_t>(vector2.dimensions())));
		}
		return vector1.get_dot(vector2);
	}

	// Help Function to Dot.
	auto euclidean_vector::get_dot(euclidean_vector const& vector) const noexcept -> double {
		return static_cast<double>(std::inner_product(this->magnitude_.get(),
		                                              this->magnitude_.get() + dimension_,
		                                              vector.magnitude_.get(),
		                                              double{0.0}));
	}

	/* Test Help Function */

	// Get euclidean norm directly without any calculating.
	auto euclidean_vector::test_get_euclidean_norm() const noexcept -> double {
		return this->euclidean_norm_;
	}

} // namespace comp6771

// Help Function
// Throw: "Dimensions of LHS(X) and RHS(Y) do not match".
auto throw_size_error_sentence(size_t lhs, size_t rhs) -> std::string {
	return std::string("Dimensions of LHS(") + std::to_string(lhs) + std::string(") and RHS(")
	       + std::to_string(rhs) + std::string(") do not match");
}

// Throw: "Index X is not valid for this euclidean_vector object".
auto throw_out_of_range_error_sentence(int index) -> std::string {
	return std::string("Index ") + std::to_string(index)
	       + std::string(" is not valid for this euclidean_vector object");
}
