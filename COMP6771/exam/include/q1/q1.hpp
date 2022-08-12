#include <cstddef>
#include <cstdint>
#include <iostream>
#include <vector>

#ifndef Q1_HPP
#	define Q1_HPP

namespace q1 {
	using map = std::vector<std::vector<char>>;

	enum class move : uint8_t {
		NN,
		SS,
		WW,
		EE,
		NW,
		NE,
		SW,
		SE,
	};

	class style {
	public:
		explicit style(char background)
		: background_(background) {
			end_ = std::vector<char>(8, '0');
			pass_ = std::vector<char>(8, '*');
		}

		style()
		: background_(' ') {
			end_ = std::vector<char>(8, '0');
			pass_ = std::vector<char>(8, '*');
		}

		virtual ~style() noexcept {
			std::destroy(pass_.begin(), pass_.end());
		}

		[[nodiscard]] virtual auto style_tile() const -> char {
			return background_;
		}

		[[nodiscard]] virtual auto style_tile(move end_move) const -> char {
			return end_[static_cast<size_t>(end_move)];
		}

		[[nodiscard]] virtual auto style_tile(move prev_move, move curr_move) const -> char {
			if (prev_move == curr_move) {
				return pass_[static_cast<size_t>(curr_move)];
			}
			else {
				return pass_[static_cast<size_t>(prev_move)];
			}
		}

	private:
		char background_;
		std::vector<char> end_;
		std::vector<char> pass_;
	};

	class detailed_style : public style {
	public:
		detailed_style(char end_1, char end_2) noexcept
		: temp(0)
		, background_('+') {
			end_1_ = std::vector<char>(8, end_1);
			end_2_ = std::vector<char>(8, end_2);
			pass_no_equal_ = std::vector<char>{'|', '|', '-', '-', '\\', '/', '/', '\\'};
			pass_equal_ = std::vector<char>{'^', 'v', '<', '>', '\\', '/', '/', '\\'};
		}

		~detailed_style() noexcept override {
			std::destroy(end_1_.begin(), end_1_.end());
			std::destroy(end_2_.begin(), end_2_.end());
			std::destroy(pass_equal_.begin(), pass_equal_.end());
			std::destroy(pass_no_equal_.begin(), pass_no_equal_.end());
		}

		[[nodiscard]] auto style_tile() const -> char override {
			return background_;
		}

		[[nodiscard]] auto style_tile(move end_move) const -> char override {
			temp++;
			return temp >= 7 ? end_2_.at(static_cast<size_t>(end_move))
			                 : end_1_.at(static_cast<size_t>(end_move));
		}

		[[nodiscard]] auto style_tile(move prev_move, move curr_move) const -> char override {
			return prev_move == curr_move ? pass_equal_.at(static_cast<size_t>(curr_move))
			                              : pass_no_equal_.at(static_cast<size_t>(curr_move));
		}

	private:
		int mutable temp;
		char background_;
		std::vector<char> end_1_;
		std::vector<char> end_2_;
		std::vector<char> pass_equal_;
		std::vector<char> pass_no_equal_;
	};

	auto at(const map& mp, int x, int y) -> char;
	auto at(map& mp, int x, int y) -> char&;

	auto make_map(const std::vector<move>& path, const style& styler) -> map;

} // namespace q1

#endif // Q1_HPP
