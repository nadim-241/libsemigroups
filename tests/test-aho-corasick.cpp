
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2023 Joe Edwards + James D. Mitchell
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

#include <fstream>

#include "libsemigroups/aho-corasick.hpp"  // for AhoCorasick

#include "catch.hpp"      // for REQUIRE, REQUIRE_THROWS_AS, REQUI...
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

namespace libsemigroups {
  using namespace literals;

  LIBSEMIGROUPS_TEST_CASE("AhoCorasick",
                          "000",
                          "initial test",
                          "[quick][aho-corasick]") {
    AhoCorasick ac;
    ac.add_word_no_checks(00101_w);
    ac.add_word_no_checks(010_w);

    REQUIRE(ac.number_of_nodes() == 8);
    REQUIRE(ac.traverse(00101_w) == 5);
    REQUIRE(ac.traverse(010_w) == 7);

    std::ofstream file("aho.gv");
    file << dot(ac).to_string();
  }

  LIBSEMIGROUPS_TEST_CASE("AhoCorasick",
                          "001",
                          "add/rm_word",
                          "[quick][aho-corasick]") {
    AhoCorasick ac;
    ac.add_word_no_checks(00101_w);

    REQUIRE(ac.number_of_nodes() == 6);
    REQUIRE(ac.traverse(00101_w) == 5);
    REQUIRE(ac.node(5).is_terminal());
    REQUIRE(ac.traverse(010_w) == 1);
    REQUIRE(!ac.node(1).is_terminal());

    ac.add_word_no_checks(010_w);
    REQUIRE(ac.number_of_nodes() == 8);
    REQUIRE(ac.traverse(010_w) == 7);
    REQUIRE(ac.node(5).is_terminal());
    REQUIRE(ac.node(7).is_terminal());

    ac.rm_word_no_checks(010_w);
    REQUIRE(ac.number_of_nodes() == 6);
    REQUIRE(ac.traverse(00101_w) == 5);
    REQUIRE(ac.node(5).is_terminal());
    REQUIRE(ac.traverse(010_w) == 1);
    REQUIRE(!ac.node(1).is_terminal());

    ac.add_word_no_checks(010_w);
    ac.add_word_no_checks(00_w);
    ac.rm_word_no_checks(00_w);

    REQUIRE(ac.number_of_nodes() == 8);
    REQUIRE(ac.traverse(00101_w) == 5);
    REQUIRE(ac.traverse(00_w) == 2);
    REQUIRE(!ac.node(ac.traverse(00_w)).is_terminal());
    REQUIRE(ac.node(5).is_terminal());

    REQUIRE(ac.traverse(010_w) == 7);
    REQUIRE(ac.node(7).is_terminal());
  }

  LIBSEMIGROUPS_TEST_CASE("AhoCorasick",
                          "002",
                          "long word",
                          "[quick][aho-corasick]") {
    using words::pow;
    using index_type = AhoCorasick::index_type;
    AhoCorasick ac;
    ac.add_word_no_checks(pow(01_w, 1000));
    ac.add_word_no_checks(pow(010_w, 10'000));
    REQUIRE(ac.number_of_nodes() == 31'998);
    for (index_type n = 0; n < ac.number_of_nodes(); ++n) {
      std::ignore = ac.suffix_link(n);
    }

    REQUIRE(ac.number_of_nodes() == 31'998);
  }

}  // namespace libsemigroups
