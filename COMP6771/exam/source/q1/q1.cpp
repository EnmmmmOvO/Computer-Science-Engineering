#include <q1/q1.hpp>

namespace q1 {
	auto at(const map& mp, int x, int y) -> char {
		return mp[std::size_t(y)][std::size_t(x)];
	}

	auto at(map& mp, int x, int y) -> char& {
		return mp[std::size_t(y)][std::size_t(x)];
	}

	auto add_capacity(bool row, bool col, map& map_, const style& styler) {
		if (row) {
			std::for_each(map_.begin(), map_.end(), [&](auto& row) {
				row.push_back(styler.style_tile());
			});
		}
		auto const& temp = new std::vector<char>(map_.size(), styler.style_tile());
		if (col)
			map_.push_back(*temp);
	}

	auto make_map(const std::vector<move>& path, const style& styler) -> map {
		auto return_map = map();
		auto row = size_t{0};
		auto col = size_t{0};
		auto last_position = move::EE;
		auto check = 0;
		return_map.push_back(*new std::vector<char>{styler.style_tile()});
		std::for_each(path.cbegin(), path.cend(), [&](auto const& path_position) {
			if (path_position == move::SE) {
				std::for_each(return_map.begin(), return_map.end(), [&](auto& row_) {
					row_.push_back(styler.style_tile());
				});
				return_map.push_back(*new std::vector<char>(return_map[0].size(), styler.style_tile()));
			}
			else if (path_position == move::SS || path_position == move::SW) {
				return_map.push_back(*new std::vector<char>(return_map[0].size(), styler.style_tile()));
			}
			else if (path_position == move::EE || path_position == move::NE) {
				std::for_each(return_map.begin(), return_map.end(), [&](auto& row_) {
					row_.push_back(styler.style_tile());
				});
			}
			if (check == 0) {
				return_map.at(col).at(row) = styler.style_tile(path_position);
			}
			else {
				return_map.at(col).at(row) = styler.style_tile(last_position, path_position);
			}
			check++;

			last_position = path_position;
			switch (path_position) {
			case move::EE: row++; break;
			case move::WW: row--; break;
			case move::NN: col--; break;
			case move::SS: col++; break;
			case move::NE: col--, row++; break;
			case move::NW: col--, row--; break;
			case move::SE: col++, row++; break;
			case move::SW: col++, row--; break;
			}
			return_map.at(col).at(row) = styler.style_tile(path_position);
			if (check == 7) {
				return_map.at(0).at(0) = styler.style_tile(path_position);
			}
		});

		return return_map;
	}

} // namespace q1
