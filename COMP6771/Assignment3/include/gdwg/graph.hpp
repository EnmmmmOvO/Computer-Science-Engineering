#ifndef GDWG_GRAPH_HPP
#define GDWG_GRAPH_HPP

#include <initializer_list>
#include <iterator>
#include <map>
#include <set>
#include <sstream>

namespace gdwg {

	template<typename N, typename E>
	class graph {
	public:
		struct value_type {
			N from;
			N to;
			E weight;
		};

		struct node_set_cmp {
			auto operator()(std::unique_ptr<N> const& left, std::unique_ptr<N> const& right) -> bool {
				return *left.get() < *right.get();
			}
			auto operator()(std::unique_ptr<N> const& left, std::unique_ptr<N> const& right) const
			   -> bool {
				return *left.get() < *right.get();
			}
		};

		struct edge_set_rule {
			auto operator()(std::unique_ptr<E> const& left, std::unique_ptr<E> const& right) -> bool {
				return *left.get() < *right.get();
			}
			auto operator()(std::unique_ptr<E> const& left, std::unique_ptr<E> const& right) const
			   -> bool {
				return *left.get() < *right.get();
			}
		};

		struct edge_map_rule {
			auto operator()(std::pair<N*, N*> left, std::pair<N*, N*> right) -> bool {
				return *left.first == *right.first ? *left.second < *right.second
				                                   : *left.first < *right.second;
			}
			auto operator()(std::pair<N*, N*> left, std::pair<N*, N*> right) const -> bool {
				return *left.first == *right.first ? *left.second < *right.second
				                                   : *left.first < *right.first;
			}
		};

		/* 2.8 - Iterator */
		class iterator {
		public:
			using value_type = graph<N, E>::value_type;
			using reference = value_type;
			using pointer = void;
			using difference_type = std::ptrdiff_t;
			using iterator_category = std::bidirectional_iterator_tag;
			using map_typename = typename std::map<std::pair<N*, N*>,
			                                       std::set<std::unique_ptr<E>, graph::edge_set_rule>,
			                                       graph::edge_map_rule>::const_iterator;
			using set_typename =
			   typename std::set<std::unique_ptr<E>, graph::edge_set_rule>::const_iterator;

			// Iterator constructor
			iterator() = default;

			// Iterator source
			auto operator*() -> reference {
				return {*map_->first.first, *map_->first.second, **set_};
			}

			// Iterator traversal
			auto operator++() -> iterator& {
				if (set_ != map_->second.end()) {
					++set_;
					if (set_ != map_->second.end())
						return *this;
				}
				set_ = ++map_ == point_->end() ? set_typename() : map_->second.begin();
				return *this;
			}

			auto operator++(int) -> iterator {
				auto temp = *this;
				++*this;
				return temp;
			}

			auto operator--() -> iterator& {
				if (set_ == set_typename()) {
					map_ = std::prev(point_->end());
					set_ = std::prev(map_->second.end());
					return *this;
				}
				else if (set_ != map_->second.begin()) {
					--set_;
					return *this;
				}
				else {
					--map_;
					set_ = std::prev(map_->second.end());
					return *this;
				}
			}

			auto operator--(int) -> iterator {
				auto temp = *this;
				--*this;
				return temp;
			}

			// Iterator comparison
			auto operator==(iterator const& other) const -> bool {
				return set_ == other.set_ && map_ == other.map_;
			};

		private:
			friend class graph;
			set_typename set_;
			map_typename map_;
			std::map<std::pair<N*, N*>, std::set<std::unique_ptr<E>, edge_set_rule>, edge_map_rule> const*
			   point_ = nullptr;
			explicit iterator(
			   std::map<std::pair<N*, N*>, std::set<std::unique_ptr<E>, edge_set_rule>, edge_map_rule> const& map,
			   map_typename map_input,
			   set_typename set_input) noexcept
			: set_(set_input)
			, map_(map_input)
			, point_(&map){};
		};

		/* 2.2 - Constructors */
		graph() noexcept {
			node_ = std::set<std::unique_ptr<N>, node_set_cmp>();
			edge_ =
			   std::map<std::pair<N*, N*>, std::set<std::unique_ptr<E>, edge_set_rule>, edge_map_rule>();
		}

		graph(std::initializer_list<N> il) noexcept {
			graph();
			std::for_each(il.begin(), il.end(), [&](N const& value) { insert_node(value); });
		}

		template<typename InputIt>
		graph(InputIt first, InputIt last) noexcept {
			graph();
			std::for_each(first, last, [&](N const& value) { insert_node(value); });
		}

		graph(graph&& other) noexcept {
			node_ = std::move(other.node_);
			edge_ = std::move(other.edge_);
			other.clear();
		}

		auto operator=(graph&& other) noexcept -> graph& {
			node_ = std::move(other.node_);
			edge_ = std::move(other.edge_);
			other.clear();
			return *this;
		}

		graph(graph const& other) noexcept {
			std::for_each(other.node_.cbegin(), other.node_.cend(), [&](auto const& it) {
				insert_node(*it);
			});

			std::for_each(other.edge_.cbegin(), other.edge_.cend(), [&](auto const& it) {
				std::for_each(it.second.cbegin(), it.second.cend(), [&](auto const& weight) {
					insert_edge(*it.first.first, *it.first.second, *weight.get());
				});
			});
		}

		auto operator=(graph const& other) noexcept -> graph& {
			std::for_each(other.node_.cbegin(), other.node_.cend(), [&](auto const& it) {
				insert_node(*it);
			});

			std::for_each(other.edge_.cbegin(), other.edge_.cend(), [&](auto const& it) {
				std::for_each(it.second.cbegin(), it.second.cend(), [&](auto const& weight) {
					insert_edge(*it.first.first, *it.first.second, *weight.get());
				});
			});
			return *this;
		}

		/* 2.3 - Modifiers */
		auto insert_node(N const& value) noexcept -> bool {
			if (is_node(value))
				return false;
			auto temp_unique_ptr = std::make_unique<N>(value);
			node_.insert(std::move(temp_unique_ptr));
			return true;
		}

		auto insert_edge(N const& src, N const& dst, E const& weight) -> bool {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				throw std::runtime_error("Cannot call gdwg::graph<N, E>::insert_edge when either src "
				                         "or dst node does not exist");
			}

			auto exist_edge = edge_.find(std::make_pair(src_node, dst_node));
			if (exist_edge != edge_.end()
			    && std::find_if(exist_edge->second.begin(), exist_edge->second.end(), [&](auto const& it) {
				       return *it.get() == weight;
			       }) != exist_edge->second.end())
			{
				return false;
			}

			edge_[std::make_pair(src_node, dst_node)].insert(std::move(std::make_unique<E>(weight)));
			return true;
		}

		auto replace_node(N const& old_data, N const& new_data) -> bool {
			auto old_node = find_node_iterator(old_data);

			if (old_node == node_.end()) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::replace_node on a node "
				                             "that doesn't exist");
			}
			else if (is_node(new_data)) {
				return false;
			}

			auto node_it = node_.extract(old_node);
			**old_node = new_data;
			node_.insert(std::move(node_it));

			auto record_edge = std::vector<std::pair<N, N>>();
			auto edge_it = edge_.begin();
			while (edge_it != edge_.end()) {
				auto check = std::find_if(record_edge.begin(), record_edge.end(), [&](auto const it) {
					return *edge_it->first.first == it.first && *edge_it->first.second == it.second;
				});
				if ((*edge_it->first.first == new_data || *edge_it->first.second == new_data)
				    && check == record_edge.end())
				{
					record_edge.push_back(std::make_pair(*edge_it->first.first, *edge_it->first.second));
					edge_.insert(std::move(edge_.extract(edge_it)));
					edge_it = edge_.begin();
				}
				else {
					++edge_it;
				}
			}
			return true;
		}

		auto merge_replace_node(N const& old_data, N const& new_data) -> void {
			auto old_node_iterator = find_node_iterator(old_data);
			auto new_node = find_node(new_data);

			if (old_node_iterator == node_.end() || new_node == nullptr) {
				throw new std::runtime_error("annot call gdwg::graph<N, E>::merge_replace_node on old "
				                             "or new data if they don't exist in the graph");
			}

			auto it = edge_.begin();
			while (it != edge_.end()) {
				if (*it->first.first == old_data && *it->first.second == old_data) {
					std::for_each(it->second.begin(), it->second.end(), [&](auto const& weight) {
						insert_edge(new_data, new_data, *weight);
					});
					it = edge_.erase(it);
				}
				else if (*it->first.first == old_data) {
					std::for_each(it->second.begin(), it->second.end(), [&](auto const& weight) {
						insert_edge(new_data, *it->first.second, *weight);
					});
					it = edge_.erase(it);
				}
				else if (*it->first.second == old_data) {
					std::for_each(it->second.begin(), it->second.end(), [&](auto const& weight) {
						insert_edge(*it->first.first, new_data, *weight);
					});
					it = edge_.erase(it);
				}
				else {
					++it;
				}
			}
			node_.erase(old_node_iterator);
		}

		auto erase_node(N const& value) -> bool {
			auto erase_node_it = find_node_iterator(value);

			if (erase_node_it == node_.end())
				return false;

			auto it = edge_.begin();
			while (it != edge_.end()) {
				if (*it->first.first == value || *it->first.second == value) {
					it = edge_.erase(it);
					continue;
				}
				++it;
			}

			node_.erase(erase_node_it);
			return true;
		}

		auto erase_edge(N const& src, N const& dst, E const& weight) -> bool {
			auto erase_src_it = find_node(src);
			auto erase_dst_it = find_node(dst);

			if (erase_dst_it == nullptr || erase_src_it == nullptr) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::erase_edge on src or dst "
				                             "if they don't exist in the graph");
			}
			else if (!is_connected(src, dst)) {
				return false;
			}

			auto edge_pair = edge_.find(std::make_pair(erase_src_it, erase_dst_it));

			for (auto weight_set = edge_pair->second.begin(); weight_set != edge_pair->second.end();
			     ++weight_set)
			{
				if (**weight_set == weight && edge_pair->second.size() == 1) {
					edge_.erase(std::make_pair(erase_src_it, erase_dst_it));
					return true;
				}
				else if (**weight_set == weight) {
					edge_pair->second.erase(weight_set);
					return true;
				}
			}

			return false;
		}

		auto erase_edge(iterator i) -> iterator {
			if (i == end())
				return i;

			auto next = i;
			++next;

			if (i.map_->second.size() == 1) {
				edge_.erase(i.map_->first);
			}
			else {
				edge_.find(i.map_->first)->second.erase(i.set_);
			}
			return next;
		}

		auto erase_edge(iterator i, iterator s) -> iterator {
			while (i != s) {
				if (i == end())
					break;
				if (i.map_->second.size() == 1) {
					auto temp_i = i;
					i++;
					edge_.erase(temp_i.map_->first);
				}
				else {
					auto temp_i = i;
					i++;
					edge_.find(temp_i.map_->first)->second.erase(temp_i.set_);
				}
			}
			return i;
		}

		auto clear() noexcept -> void {
			node_.clear();
			edge_.clear();
		}

		/* 2.4 - Accessors */
		[[nodiscard]] auto is_node(N const& value) -> bool {
			return find_node(value) != nullptr;
		}

		[[nodiscard]] auto is_node(N const& value) const -> bool {
			return find_node(value) != nullptr;
		}

		[[nodiscard]] auto empty() -> bool {
			return node_.size() == 0;
		}

		[[nodiscard]] auto empty() const -> bool {
			return node_.size() == 0;
		}

		[[nodiscard]] auto is_connected(N const& src, N const& dst) -> bool {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::is_connected if src or "
				                             "dst node don't exist in the graph");
			}

			return edge_.find(std::make_pair(src_node, dst_node)) != edge_.end();
		}

		[[nodiscard]] auto is_connected(N const& src, N const& dst) const -> bool {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::is_connected if src or "
				                             "dst node don't exist in the graph");
			}

			return edge_.find(std::make_pair(src_node, dst_node)) != edge_.end();
		}

		[[nodiscard]] auto nodes() -> std::vector<N> {
			auto node_vector = std::vector<N>();
			std::for_each(node_.cbegin(), node_.end(), [&](auto const& it) {
				node_vector.push_back(*it);
			});
			return node_vector;
		}

		[[nodiscard]] auto nodes() const -> std::vector<N> {
			auto node_vector = std::vector<N>();
			std::for_each(node_.cbegin(), node_.end(), [&](auto const& it) {
				node_vector.push_back(*it);
			});
			return node_vector;
		}

		[[nodiscard]] auto weights(N const& src, N const& dst) -> std::vector<E> {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::weights if src or dst "
				                             "node "
				                             "don't exist in the graph");
			}

			auto weight_vector = std::vector<E>();
			auto weight_set = edge_.find(std::make_pair(src_node, dst_node));
			if (weight_set != edge_.end()) {
				std::for_each(weight_set->second.cbegin(),
				              weight_set->second.cend(),
				              [&](auto const& it) { weight_vector.push_back(*it.get()); });
			}
			return weight_vector;
		}

		[[nodiscard]] auto weights(N const& src, N const& dst) const -> std::vector<E> {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				throw new std::runtime_error("Cannot call gdwg::graph<N, E>::weights if src or dst "
				                             "node "
				                             "don't exist in the graph");
			}

			auto weight_vector = std::vector<E>();
			auto const& weight_set = edge_.find(std::make_pair(src_node, dst_node));
			if (weight_set != edge_.end()) {
				std::for_each(weight_set->second.cbegin(),
				              weight_set->second.cend(),
				              [&](auto const& it) { weight_vector.push_back(*it.get()); });
			}
			return weight_vector;
		}

		[[nodiscard]] auto find(N const& src, N const& dst, E const& weight) -> iterator {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				return iterator(edge_, edge_.end(), {});
			}

			auto const& weight_set = edge_.find(std::make_pair(src_node, dst_node));

			if (weight_set == edge_.end()) {
				return iterator(edge_, edge_.end(), {});
			}

			auto const& edge_iterator = find_edge_iterator(weight, weight_set->second);
			return edge_iterator == weight_set->second.end()
			          ? iterator(edge_, edge_.end(), {})
			          : iterator(edge_, weight_set, edge_iterator);
		}

		[[nodiscard]] auto find(N const& src, N const& dst, E const& weight) const -> iterator {
			auto src_node = find_node(src);
			auto dst_node = find_node(dst);

			if (src_node == nullptr || dst_node == nullptr) {
				return iterator(edge_, edge_.end(), {});
			}

			auto const& weight_set = edge_.find(std::make_pair(src_node, dst_node));

			if (weight_set == edge_.end()) {
				return iterator(edge_, edge_.end(), {});
			}

			auto const& edge_iterator = find_edge_iterator(weight, weight_set->second);
			return edge_iterator == weight_set->second.end()
			          ? iterator(edge_, edge_.end(), {})
			          : iterator(edge_, weight_set, edge_iterator);
		}

		[[nodiscard]] auto connections(N const& src) -> std::vector<N> {
			auto src_node = find_node(src);
			if (src_node == nullptr) {
				throw std::runtime_error("Cannot call gdwg::graph<N, E>::connections if src doesn't "
				                         "exist in the graph");
			}

			auto connection_node = std::vector<N>();
			std::for_each(edge_.cbegin(), edge_.cend(), [&](auto const& pair) {
				if (pair.first.first == src_node) {
					connection_node.push_back(*pair.first.second);
				}
			});

			return connection_node;
		}

		[[nodiscard]] auto connections(N const& src) const -> std::vector<N> {
			auto src_node = find_node(src);
			if (src_node == nullptr) {
				throw std::runtime_error("Cannot call gdwg::graph<N, E>::connections if src doesn't "
				                         "exist in the graph");
			}

			auto connection_node = std::vector<N>();
			std::for_each(edge_.cbegin(), edge_.cend(), [&](auto const& pair) {
				if (pair.first.first == src_node) {
					connection_node.push_back(*pair.first.second);
				}
			});

			return connection_node;
		}

		/* 2.5 - Iterator access */
		[[nodiscard]] auto begin() const -> iterator {
			return edge_.empty()
			          ? iterator(edge_, edge_.begin(), decltype(edge_.begin()->second.begin()){})
			          : iterator(edge_, edge_.begin(), edge_.begin()->second.begin());
		}

		[[nodiscard]] auto end() const -> iterator {
			return iterator(edge_, edge_.end(), {});
		}

		/* 2.6 - Comparisons */
		[[nodiscard]] auto operator==(graph const& other) -> bool {
			if (node_.size() != other.node_.size() || edge_.size() != other.edge_.size()) {
				return false;
			}

			auto it = node_.begin();
			auto other_it = other.node_.begin();
			for (; it != node_.end(); ++it, ++other_it) {
				if (*it->get() != *other_it->get())
					return false;
			}

			auto edge_it = edge_.begin();
			auto other_edge_it = other.edge_.begin();
			for (; edge_it != edge_.end(); ++edge_it, ++other_edge_it) {
				if (*edge_it->first.first != *other_edge_it->first.first
				    || *edge_it->first.second != *other_edge_it->first.second
				    || edge_it->second.size() != other_edge_it->second.size()
				    || all_edge(edge_it->second) != other.all_edge(other_edge_it->second))
				{
					return false;
				}
			}
			return true;
		}

		[[nodiscard]] auto operator==(graph const& other) const -> bool {
			if (node_.size() != other.node_.size() || edge_.size() != other.edge_.size()) {
				return false;
			}

			auto it = node_.begin();
			auto other_it = other.node_.begin();
			for (; it != node_.end(); ++it, ++other_it) {
				if (*it->get() != *other_it->get())
					return false;
			}

			auto edge_it = edge_.begin();
			auto other_edge_it = other.edge_.begin();
			for (; edge_it != edge_.end(); ++edge_it, ++other_edge_it) {
				if (*edge_it->first.first != *other_edge_it->first.first
				    || *edge_it->first.second != *other_edge_it->first.second
				    || edge_it->second.size() != other_edge_it->second.size()
				    || all_edge(edge_it->second) != other.all_edge(other_edge_it->second))
				{
					return false;
				}
			}
			return true;
		}

		/* 2.7 - Extractor */
		friend auto operator<<(std::ostream& os, graph const& g) -> std::ostream& {
			std::for_each(g.node_.cbegin(), g.node_.cend(), [&](auto const& node_it) {
				os << *node_it << " (" << std::endl;
				std::for_each(g.edge_.cbegin(), g.edge_.cend(), [&](auto const& pair) {
					if (*pair.first.first == *node_it) {
						auto const& set = pair.second;
						std::for_each(set.cbegin(), set.cend(), [&](auto const& it) {
							os << "  " << *pair.first.second << " | " << *it << std::endl;
						});
					}
				});
				os << ")" << std::endl;
			});

			return os;
		}

	private:
		std::set<std::unique_ptr<N>, node_set_cmp> node_;
		std::map<std::pair<N*, N*>, std::set<std::unique_ptr<E>, edge_set_rule>, edge_map_rule> edge_;

		auto find_node(N const& value) noexcept -> N* {
			auto it = find_node_iterator(value);
			return it == node_.end() ? nullptr : it->get();
		}

		auto find_node(N const& value) const noexcept -> N* {
			auto it = find_node_iterator(value);
			return it == node_.end() ? nullptr : it->get();
		}

		auto find_node_iterator(N const& value) noexcept ->
		   typename std::set<std::unique_ptr<N>>::iterator {
			auto low = int{0};
			auto high = static_cast<int>(node_.size()) - 1;
			while (low <= high) {
				auto it = std::next(node_.begin(), (low + high) / 2);
				if (*it->get() == value) {
					return it;
				}
				else if (*it->get() > value) {
					high = (low + high) / 2 - 1;
				}
				else {
					low = (low + high) / 2 + 1;
				}
			}
			return node_.end();
		}

		auto find_node_iterator(N const& value) const noexcept ->
		   typename std::set<std::unique_ptr<N>>::iterator {
			auto low = int{0};
			auto high = static_cast<int>(node_.size()) - 1;
			while (low <= high) {
				auto it = std::next(node_.begin(), (low + high) / 2);
				if (*it->get() == value) {
					return it;
				}
				else if (*it->get() > value) {
					high = (low + high) / 2 - 1;
				}
				else {
					low = (low + high) / 2 + 1;
				}
			}
			return node_.end();
		}

		auto
		find_edge_iterator(E const& value,
		                   std::set<std::unique_ptr<E>, edge_set_rule> const& edge_set) const noexcept
		   -> typename std::set<std::unique_ptr<E>>::iterator {
			auto low = int{0};
			auto high = static_cast<int>(edge_set.size()) - 1;
			while (low <= high) {
				auto it = std::next(edge_set.begin(), (low + high) / 2);
				if (*it->get() == value) {
					return it;
				}
				else if (*it->get() > value) {
					high = (low + high) / 2 - 1;
				}
				else {
					low = (low + high) / 2 + 1;
				}
			}
			return edge_set.end();
		}

		auto all_edge(std::set<std::unique_ptr<E>, edge_set_rule> const& edge_set) const noexcept
		   -> std::vector<E> {
			auto vector_edge = std::vector<E>();
			std::for_each(edge_set.begin(), edge_set.end(), [&](auto const& it) {
				vector_edge.push_back(*it);
			});
			return vector_edge;
		}
	};
} // namespace gdwg

#endif // GDWG_GRAPH_HPP
