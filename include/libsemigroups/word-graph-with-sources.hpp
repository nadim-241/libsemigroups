//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2022-23 James D. Mitchell
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

// This file contains a declaration of a class for WordGraphs with
// additional information about the edges leading into every node (not only
// those leaving every node).
//
// In the comments in this file we refer to "valid nodes", this means nodes in
// the graph where the values returned by first_source_no_checks and
// next_source_no_checks are valid (i.e. correspond to edges in the underlying
// WordGraph that point into the current node). Validity of nodes is not tracked
// by WordGraphWithSources, and it is the responsibility of the caller to ensure
// that nodes are valid where required by the various member functions of
// WordGraphWithSources.

#ifndef LIBSEMIGROUPS_WORD_GRAPH_WITH_SOURCES_HPP_
#define LIBSEMIGROUPS_WORD_GRAPH_WITH_SOURCES_HPP_

// TODO:
// * test file
// * doc
// * add _no_checks where appropriate

#include <cstddef>  // for size_t
#include <stack>    // for stack
#include <utility>  // for pair
#include <vector>   // for vector

#include "config.hpp"      // for LIBSEMIGROUPS_DEBUG
#include "constants.hpp"   // for UNDEFINED
#include "types.hpp"       // for letter_type
#include "word-graph.hpp"  // for WordGraph

#include "detail/containers.hpp"  // for DynamicArray2

namespace libsemigroups {
  template <typename Node>
  class WordGraphWithSources : public WordGraph<Node> {
   public:
    using node_type  = Node;
    using label_type = typename WordGraph<Node>::label_type;
    using size_type  = typename WordGraph<Node>::size_type;

   private:
    detail::DynamicArray2<node_type> _preim_init;
    detail::DynamicArray2<node_type> _preim_next;

   public:
    // So that we can use out_degree and number_of_nodes in assertions
    using WordGraph<Node>::out_degree;
    using WordGraph<Node>::number_of_nodes;

    explicit WordGraphWithSources(size_type m = 0, size_type n = 0)
        : WordGraph<node_type>(m, n),
          _preim_init(n, m, UNDEFINED),
          _preim_next(n, m, UNDEFINED) {}

    void init(size_type m, size_type n);

    template <typename ThatNode>
    explicit WordGraphWithSources(WordGraph<ThatNode> const& that);

    template <typename ThatNode>
    void init(WordGraph<ThatNode> const& that);

    template <typename ThatNode>
    explicit WordGraphWithSources(WordGraph<ThatNode>&& that);

    template <typename ThatNode>
    void init(WordGraph<ThatNode>&& that);

    WordGraphWithSources(WordGraphWithSources&&)                 = default;
    WordGraphWithSources(WordGraphWithSources const&)            = default;
    WordGraphWithSources& operator=(WordGraphWithSources const&) = default;
    WordGraphWithSources& operator=(WordGraphWithSources&&)      = default;

    ~WordGraphWithSources();

    // the template is for uniformity of interface with FelschGraph
    template <bool = true>
    void set_target_no_checks(node_type c, label_type x, node_type d) noexcept {
      LIBSEMIGROUPS_ASSERT(c < number_of_nodes());
      LIBSEMIGROUPS_ASSERT(x < out_degree());
      LIBSEMIGROUPS_ASSERT(d < number_of_nodes());
      WordGraph<node_type>::set_target_no_checks(c, x, d);
      add_source_no_checks(d, x, c);
    }

    void remove_target_no_checks(node_type c, label_type x) noexcept {
      LIBSEMIGROUPS_ASSERT(c < number_of_nodes());
      LIBSEMIGROUPS_ASSERT(x < out_degree());
      remove_source_no_checks(WordGraph<Node>::target_no_checks(c, x), x, c);
      WordGraph<node_type>::remove_target_no_checks(c, x);
    }

    void add_nodes(size_type m) {
      WordGraph<node_type>::add_nodes(m);
      _preim_init.add_rows(m);
      _preim_next.add_rows(m);
    }

    void add_to_out_degree(size_type m) {
      _preim_init.add_cols(m);
      _preim_next.add_cols(m);
      WordGraph<node_type>::add_to_out_degree(m);
    }

    inline node_type first_source_no_checks(node_type   c,
                                            letter_type x) const noexcept {
      LIBSEMIGROUPS_ASSERT(c < number_of_nodes());
      LIBSEMIGROUPS_ASSERT(x < out_degree());
      LIBSEMIGROUPS_ASSERT(c < _preim_init.number_of_rows());
      LIBSEMIGROUPS_ASSERT(x < _preim_init.number_of_cols());
      return _preim_init.get(c, x);
    }

    inline node_type next_source_no_checks(node_type   c,
                                           letter_type x) const noexcept {
      LIBSEMIGROUPS_ASSERT(c < number_of_nodes());
      LIBSEMIGROUPS_ASSERT(x < out_degree());
      LIBSEMIGROUPS_ASSERT(c < _preim_next.number_of_rows());
      LIBSEMIGROUPS_ASSERT(x < _preim_next.number_of_cols());
      return _preim_next.get(c, x);
    }

    void induced_subgraph_no_checks(node_type first, node_type last);

    // The permutation q must map the valid nodes to the [0, .. , n), where
    // n is the number of valid nodes, and p = q ^ -1.
    void permute_nodes_no_checks(std::vector<node_type> const& p,
                                 std::vector<node_type> const& q,
                                 size_t                        n);

    // Swaps valid nodes c and d, if c or d is not valid, then this will
    // fail spectacularly (no checks are performed)
    void swap_nodes_no_checks(node_type c, node_type d);

    // Rename c to d, i.e. node d has the exact same in- and out-neighbours
    // as c after this is called. Assumed that c is valid when this function
    // is called, and that d is valid after it is called. This is a
    // one-sided version of swap nodes.
    void rename_node_no_checks(node_type c, node_type d);

    template <typename NewEdgeFunc, typename IncompatibleFunc>
    void merge_nodes_no_checks(node_type          min,
                               node_type          max,
                               NewEdgeFunc&&      new_edge,
                               IncompatibleFunc&& incompat);

    // Is d a source of c under x? This is costly!
    bool is_source_no_checks(node_type c, label_type x, node_type d) const;

    void remove_all_sources_and_targets_no_checks(node_type c);
    void remove_all_sources_no_checks(node_type c);

    void add_source_no_checks(node_type c, label_type x, node_type d) noexcept;

    template <typename It>
    void rebuild_sources_no_checks(It first, It last);

    // TODO remove
    // Copied from word graph-with-sources.hpp in fp-inverse-monoids branch
    // void shrink_to_fit(size_type m) {
    //   this->restrict(m);
    //   _preim_init.shrink_rows_to(m);
    //   _preim_next.shrink_rows_to(m);
    // }

    // TODO to cpp/tpp file
    void disjoint_union_inplace(WordGraph<Node> const& that) {
      size_t N = number_of_nodes();
      add_nodes(that.number_of_nodes());
      for (auto s : that.nodes()) {
        for (auto [a, t] : that.labels_and_targets_no_checks(s)) {
          if (t != UNDEFINED) {
            set_target_no_checks(s + N, a, t + N);
          }
        }
      }
    }

   private:
    void remove_source_no_checks(node_type cx, label_type x, node_type d);
    void replace_target_no_checks(node_type c, label_type x, node_type d);
    void replace_source_no_checks(node_type  c,
                                  node_type  d,
                                  label_type x,
                                  node_type  cx);
  };

  template <typename Node>
  class HopcroftKarp {
   private:
    using word_graph_type = WordGraph<Node>;
    using node_type       = Node;
    using label_type      = typename word_graph_type::label_type;

    detail::Duf<>                               _uf;
    std::stack<std::pair<node_type, node_type>> _stck;
    WordGraph<Node> const*                      _wg1;
    WordGraph<Node> const*                      _wg2;

    [[nodiscard]] node_type find(node_type n, label_type a) const {
      // Check which word graph q1 and q2 belong to. nodes with labels
      // from 0 to N1 correspond to nodes in wg1; above N1 corresponds to
      // wg2.
      auto N1 = _wg1->number_of_nodes();
      if (n < N1) {
        return _uf.find(_wg1->target_no_checks(n, a));
      } else {
        return _uf.find(_wg2->target_no_checks(n - N1, a) + N1);
      }
    }

   public:
    HopcroftKarp() = default;

    HopcroftKarp(WordGraph<Node> const& wg1, WordGraph<Node> const& wg2)
        : HopcroftKarp() {
      init(wg1, wg2);
    }

    HopcroftKarp& init(WordGraph<Node> const& wg1, WordGraph<Node> const& wg2) {
      auto const N1 = wg1->number_of_nodes();
      auto const N2 = wg2->number_of_nodes();

      if (wg1.out_degree() != wg2->out_degree()) {
        LIBSEMIGROUPS_EXCEPTION(
            "the arguments (word graphs) must have the same "
            "out-degree, found out-degrees {} and {}",
            wg1->out_degree(),
            wg2->out_degree());
      }
      _uf.init(N1 + N2);
      _stck.clear();
    }

    // Return the partition obtained by Hopcroft and Karp's Algorithm for
    // checking if two finite state automata accept the same language, with
    // given start nodes root1 and root2.
    detail::Duf<> const& operator()(node_type root1, node_type root2) {
      word_graph::validate_node(_wg1, root1);
      word_graph::validate_node(_wg2, root2);

      auto const M  = _wg1->out_degree();
      auto const N1 = _wg1->number_of_nodes();
      auto const N2 = _wg2->number_of_nodes();

      _uf.unite(root1, root2 + N1);

      // 0 .. N1 - 1, N1  .. N1 + N2 -1
      LIBSEMIGROUPS_ASSERT(_stck.empty());
      _stck.emplace(root1, root2 + N1);

      // Traverse wg1 and wg2, uniting the target nodes at each stage
      while (!_stck.empty()) {
        auto [q1, q2] = _stck.top();
        _stck.pop();
        for (label_type a = 0; a < M; ++a) {
          node_type r1 = find(q1, a), r2 = find(q2, a);
          if (r1 != r2) {
            _uf.unite(r1, r2);
            _stck.emplace(r1, r2);
          }
        }
      }
      return _uf;
    }
  };
}  // namespace libsemigroups

#include "word-graph-with-sources.tpp"

#endif  // LIBSEMIGROUPS_WORD_GRAPH_WITH_SOURCES_HPP_
