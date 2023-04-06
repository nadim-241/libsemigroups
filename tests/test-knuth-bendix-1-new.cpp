// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019 James D. Mitchell
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

// This file is one of six that contains tests for the KnuthBendix classes. In
// a mostly vain attempt to speed up compilation the tests are split across 6
// files as follows:
//
// 1: contains quick tests for fpsemigroup::KnuthBendix created from rules and
//    all commented out tests.
//
// 2: contains more quick tests for fpsemigroup::KnuthBendix created from rules
//
// 3: contains yet more quick tests for fpsemigroup::KnuthBendix created from
//    rules
//
// 4: contains standard and extreme test for fpsemigroup::KnuthBendix created
//    from rules
//
// 5: contains tests for fpsemigroup::KnuthBendix created from FroidurePin
//    instances
//
// 6: contains tests for congruence::KnuthBendix.

// TODO(later)
// 1. The other examples from Sims' book (Chapters 5 and 6) which use
//    reduction orderings different from shortlex
// 2. Examples from MAF

// #define CATCH_CONFIG_ENABLE_PAIR_STRINGMAKER

#include <string>  // for string
#include <vector>  // for vector

#include "catch.hpp"      // for REQUIRE, REQUIRE_NOTHROW, REQUIRE_THROWS_AS
#include "test-main.hpp"  // for LIBSEMIGROUPS_TEST_CASE

#include "libsemigroups/config.hpp"             // for LIBSEMIGROUPS_DEBUG
#include "libsemigroups/constants.hpp"          // for POSITIVE_INFINITY
#include "libsemigroups/knuth-bendix-new.hpp"   // for KnuthBendix, operator<<
#include "libsemigroups/make-froidure-pin.hpp"  // for to_froidure_pin
#include "libsemigroups/obvinf.hpp"             // for word_type
#include "libsemigroups/ranges.hpp"             // for ReportGuard
#include "libsemigroups/report.hpp"             // for ReportGuard
#include "libsemigroups/types.hpp"              // for word_type

#include <rx/ranges.hpp>

namespace libsemigroups {
  using namespace rx;

  struct LibsemigroupsException;
  constexpr bool REPORT = false;

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "000",
                          "confluent fp semigroup 1 (infinite)",
                          "[quick][knuth-bendix]") {
    auto                      rg = ReportGuard(REPORT);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule(p, "ab", "ba");
    presentation::add_rule(p, "ac", "ca");
    presentation::add_rule(p, "aa", "a");
    presentation::add_rule(p, "ac", "a");
    presentation::add_rule(p, "ca", "a");
    presentation::add_rule(p, "bb", "bb");
    presentation::add_rule(p, "bc", "cb");
    presentation::add_rule(p, "bbb", "b");
    presentation::add_rule(p, "bc", "b");
    presentation::add_rule(p, "cb", "b");
    presentation::add_rule(p, "a", "b");

    KnuthBendix kb(p);

    REQUIRE(kb.number_of_active_rules() == 4);
    REQUIRE(kb.confluent());
    REQUIRE(kb.normal_form("ca") == "a");
    REQUIRE(kb.normal_form("ac") == "a");
    REQUIRE(kb.equal_to("ca", "a"));
    REQUIRE(kb.equal_to("ac", "a"));
    REQUIRE(kb.size() == POSITIVE_INFINITY);
    REQUIRE(is_obviously_infinite(kb));

    // TODO uncomment
    // REQUIRE(std::vector<std::string>(kb.cbegin_normal_forms("abc", 0, 5),
    //                                  kb.cend_normal_forms())
    //         == std::vector<std::string>({"a", "c", "cc", "ccc", "cccc"}));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "001",
                          "confluent fp semigroup 2 (infinite) ",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule(p, "ac", "ca");
    presentation::add_rule(p, "aa", "a");
    presentation::add_rule(p, "ac", "a");
    presentation::add_rule(p, "ca", "a");
    presentation::add_rule(p, "bb", "bb");
    presentation::add_rule(p, "bc", "cb");
    presentation::add_rule(p, "bbb", "b");
    presentation::add_rule(p, "bc", "b");
    presentation::add_rule(p, "cb", "b");
    presentation::add_rule(p, "a", "b");

    KnuthBendix kb(p);

    REQUIRE(kb.confluent());
    REQUIRE(kb.number_of_active_rules() == 4);
    REQUIRE(is_obviously_infinite(kb));
    // TODO uncomment
    // REQUIRE(std::vector<std::string>(kb.cbegin_normal_forms("abc", 0, 5),
    //                                  kb.cend_normal_forms())
    //         == std::vector<std::string>({"a", "c", "cc", "ccc", "cccc"}));
    REQUIRE(kb.size() == POSITIVE_INFINITY);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "002",
                          "confluent fp semigroup 3 (infinite) ",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.alphabet("012");
    presentation::add_rule(p, "01", "10");
    presentation::add_rule(p, "02", "20");
    presentation::add_rule(p, "00", "0");
    presentation::add_rule(p, "02", "0");
    presentation::add_rule(p, "20", "0");
    presentation::add_rule(p, "11", "11");
    presentation::add_rule(p, "12", "21");
    presentation::add_rule(p, "111", "1");
    presentation::add_rule(p, "12", "1");
    presentation::add_rule(p, "21", "1");
    presentation::add_rule(p, "0", "1");

    KnuthBendix kb(p);

    REQUIRE(kb.number_of_active_rules() == 4);
    REQUIRE(kb.confluent());
    REQUIRE(kb.number_of_active_rules() == 4);
    REQUIRE(kb.size() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(1).max(2) | to_strings(p.alphabet()) | to_vector())
            == std::vector<std::string>({"0", "2"}));

    REQUIRE((nf.min(1).max(12) | to_strings(p.alphabet()) | to_vector())
            == std::vector<std::string>({"0",
                                         "2",
                                         "22",
                                         "222",
                                         "2222",
                                         "22222",
                                         "222222",
                                         "2222222",
                                         "22222222",
                                         "222222222",
                                         "2222222222",
                                         "22222222222"}));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "003",
                          "non-confluent fp semigroup from "
                          "wikipedia (infinite)",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("01");
    presentation::add_rule(p, "000", "");
    presentation::add_rule(p, "111", "");
    presentation::add_rule(p, "010101", "");

    KnuthBendix kb(p);
    REQUIRE(kb.presentation().alphabet() == "01");
    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 4);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);

    REQUIRE((nf.min(0).max(5) | to_strings(p.alphabet()) | to_vector())
            == std::vector<std::string>(
                {"",     "0",    "1",    "00",   "01",   "10",   "11",
                 "001",  "010",  "011",  "100",  "101",  "110",  "0010",
                 "0011", "0100", "0101", "0110", "1001", "1011", "1101"}));
    REQUIRE(
        (nf.min(0).max(10) | to_strings(p.alphabet())
         | all_of([&kb](auto const& w) { return kb.normal_form(w) == w; })));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "004",
                          "Example 5.1 in Sims (infinite)",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("abcd");
    presentation::add_rule(p, "ab", "");
    presentation::add_rule(p, "ba", "");
    presentation::add_rule(p, "cd", "");
    presentation::add_rule(p, "dc", "");
    presentation::add_rule(p, "ca", "ac");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 8);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(0).max(5) | to_strings(p.alphabet()) | to_vector())
            == std::vector<std::string>(
                {"",     "a",    "b",    "c",    "d",    "aa",   "ac",
                 "ad",   "bb",   "bc",   "bd",   "cc",   "dd",   "aaa",
                 "aac",  "aad",  "acc",  "add",  "bbb",  "bbc",  "bbd",
                 "bcc",  "bdd",  "ccc",  "ddd",  "aaaa", "aaac", "aaad",
                 "aacc", "aadd", "accc", "addd", "bbbb", "bbbc", "bbbd",
                 "bbcc", "bbdd", "bccc", "bddd", "cccc", "dddd"}));
    REQUIRE(
        (nf.min(0).max(6) | to_strings(p.alphabet())
         | all_of([&kb](auto const& w) { return kb.normal_form(w) == w; })));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "005",
                          "Example 5.1 in Sims (infinite)",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("aAbB");
    presentation::add_inverse_rules(p, "AaBb");
    presentation::add_rule(p, "ba", "ab");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 8);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == POSITIVE_INFINITY);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE((nf.min(0).max(5) | to_strings("abcd") | to_vector())
            == std::vector<std::string>(
                {"",     "a",    "b",    "c",    "d",    "aa",   "ac",
                 "ad",   "bb",   "bc",   "bd",   "cc",   "dd",   "aaa",
                 "aac",  "aad",  "acc",  "add",  "bbb",  "bbc",  "bbd",
                 "bcc",  "bdd",  "ccc",  "ddd",  "aaaa", "aaac", "aaad",
                 "aacc", "aadd", "accc", "addd", "bbbb", "bbbc", "bbbd",
                 "bbcc", "bbdd", "bccc", "bddd", "cccc", "dddd"}));
    REQUIRE(
        (nf.min(0).max(6) | to_strings(p.alphabet())
         | all_of([&kb](auto const& w) { return kb.normal_form(w) == w; })));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "006",
                          "Example 5.3 in Sims",
                          "[quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("ab");
    presentation::add_rule(p, "aa", "");
    presentation::add_rule(p, "bbb", "");
    presentation::add_rule(p, "ababab", "");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 6);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == 12);

    auto nf = knuth_bendix::normal_forms(kb);
    REQUIRE(nf.count() == 12);

    REQUIRE((nf | to_strings(p.alphabet()) | to_vector())
            == std::vector<std::string>({"",
                                         "a",
                                         "b",
                                         "ab",
                                         "ba",
                                         "bb",
                                         "aba",
                                         "abb",
                                         "bab",
                                         "bba",
                                         "babb",
                                         "bbab"}));
    REQUIRE(
        (nf.min(0).max(6) | to_strings(p.alphabet())
         | all_of([&kb](auto const& w) { return kb.normal_form(w) == w; })));
  }
  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "007",
                          "Example 5.4 in Sims",
                          "[quick][knuth-bendix]") {
    auto                      rg = ReportGuard(REPORT);
    Presentation<std::string> p;
    p.contains_empty_word(true);
    p.alphabet("Bab");
    presentation::add_rule(p, "aa", "");
    presentation::add_rule(p, "bB", "");
    presentation::add_rule(p, "bbb", "");
    presentation::add_rule(p, "ababab", "");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 11);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == 12);

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(5)
              | to_strings(p.alphabet());
    REQUIRE((nf | to_vector())
            == std::vector<std::string>({"B",
                                         "a",
                                         "b",
                                         "Ba",
                                         "aB",
                                         "ab",
                                         "ba",
                                         "BaB",
                                         "Bab",
                                         "aBa",
                                         "baB"}));
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "008",
                          "Example 6.4 in Sims (size 168)",
                          "[no-valgrind][quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.alphabet("abc");
    p.contains_empty_word(true);

    presentation::add_rule(p, "aa", "");
    presentation::add_rule(p, "bc", "");
    presentation::add_rule(p, "bbb", "");
    presentation::add_rule(p, "ababababababab", "");
    presentation::add_rule(p, "abacabacabacabac", "");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    REQUIRE(!is_obviously_infinite(kb));
    // REQUIRE(!kb.is_obviously_finite());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 40);
    REQUIRE(kb.confluent());
    REQUIRE(kb.normal_form("cc") == "b");
    REQUIRE(kb.normal_form("ccc") == "");
    REQUIRE(kb.size() == 168);

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(5)
              | to_strings(p.alphabet());
    REQUIRE((nf | to_vector())
            == std::vector<std::string>(
                {"a",    "b",    "c",    "ab",   "ac",   "ba",   "ca",
                 "aba",  "aca",  "bab",  "bac",  "cab",  "cac",  "abab",
                 "abac", "acab", "acac", "baba", "baca", "caba", "caca"}));
    auto S = to_froidure_pin(kb);
    REQUIRE(S.size() == 168);
    REQUIRE(S.generator(2).string(kb) == "c");
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "009",
                          "random example",
                          "[quick][knuth-bendix][no-valgrind]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.alphabet("012");

    presentation::add_rule(p, "000", "2");
    presentation::add_rule(p, "111", "2");
    presentation::add_rule(p, "010101", "2");
    presentation::add_identity_rules(p, '2');

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 9);
    REQUIRE(kb.confluent());

    auto& ad = kb.gilman_digraph();
    REQUIRE(ad.number_of_nodes() == 9);
    REQUIRE(ad.number_of_edges() == 13);
    REQUIRE(!action_digraph_helper::is_acyclic(ad));

    auto fp = to_froidure_pin(kb);
    fp.enumerate(100);

    auto expected
        = iterator_range(fp.cbegin_normal_forms(), fp.cend_normal_forms());

    Paths paths(ad);
    paths.from(0).min(1).max(fp.current_max_word_length() + 1);

    REQUIRE(equal(expected, paths));

    auto nf = knuth_bendix::normal_forms(kb).min(1).max(5)
              | to_strings(p.alphabet());
    REQUIRE((nf | to_vector())
            == std::vector<std::string>(
                {"0",    "1",    "2",    "00",   "01",   "10",   "11",
                 "001",  "010",  "011",  "100",  "101",  "110",  "0010",
                 "0011", "0100", "0101", "0110", "1001", "1011", "1101"}));
  }

  LIBSEMIGROUPS_TEST_CASE(
      "KnuthBendix",
      "010",
      "SL(2, 7) from Chapter 3, Proposition 1.5 in NR (size 336)",
      "[no-valgrind][quick][knuth-bendix]") {
    auto rg = ReportGuard(REPORT);

    Presentation<std::string> p;
    p.alphabet("abAB");
    p.contains_empty_word(true);

    presentation::add_rule(p, "aaaaaaa", "");
    presentation::add_rule(p, "bb", "ababab");
    presentation::add_rule(p, "bb", "aaaabaaaabaaaabaaaab");
    presentation::add_rule(p, "aA", "");
    presentation::add_rule(p, "Aa", "");
    presentation::add_rule(p, "bB", "");
    presentation::add_rule(p, "Bb", "");

    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());

    kb.run();
    REQUIRE(kb.number_of_active_rules() == 152);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == 336);

    // Test copy constructor
    auto T = to_froidure_pin(kb);
    auto S = T.copy_closure({T.generator(0)});

    REQUIRE(S.size() == 336);
    REQUIRE(S.number_of_generators() == 4);

    auto& ad = kb.gilman_digraph();
    REQUIRE(ad.number_of_nodes() == 232);
    REQUIRE(ad.number_of_edges() == 265);
    REQUIRE(action_digraph_helper::is_acyclic(ad));
    Paths paths(ad);
    paths.from(0).min(0).max(13);
    REQUIRE(paths.count() == 336);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "011",
                          "F(2, 5) - Chapter 9, Section 1 in NR (size 11)",
                          "[knuth-bendix][quick]") {
    auto                      rg = ReportGuard(REPORT);
    Presentation<std::string> p;
    p.alphabet("abcde");

    presentation::add_rule(p, "ab", "c");
    presentation::add_rule(p, "bc", "d");
    presentation::add_rule(p, "cd", "e");
    presentation::add_rule(p, "de", "a");
    presentation::add_rule(p, "ea", "b");
    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 24);
    REQUIRE(kb.confluent());
    REQUIRE(kb.size() == 11);

    auto& ad = kb.gilman_digraph();
    REQUIRE(ad.number_of_nodes() == 8);
    REQUIRE(ad.number_of_edges() == 11);
    REQUIRE(action_digraph_helper::is_acyclic(ad));
    Paths paths(ad);
    paths.from(0).min(0).max(5);
    REQUIRE(paths.count() == 12);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "012",
                          "Reinis example 1",
                          "[quick][knuth-bendix]") {
    auto                      rg = ReportGuard(REPORT);
    Presentation<std::string> p;
    p.alphabet("abc");

    presentation::add_rule(p, "a", "abb");
    presentation::add_rule(p, "b", "baa");
    KnuthBendix kb(p);

    REQUIRE(!kb.confluent());
    kb.run();
    REQUIRE(kb.number_of_active_rules() == 4);

    auto& ad = kb.gilman_digraph();
    REQUIRE(ad.number_of_nodes() == 7);
    REQUIRE(ad.number_of_edges() == 17);
    REQUIRE(!action_digraph_helper::is_acyclic(ad));
    Paths paths(ad);
    paths.from(0).min(0).max(10);
    REQUIRE(paths.count() == 13'044);
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "013",
                          "redundant_rule (std::string)",
                          "[quick][knuth-bendix]") {
    auto                      rg = ReportGuard(REPORT);
    Presentation<std::string> p;
    p.alphabet("abc");
    presentation::add_rule_and_check(p, "a", "abb");
    presentation::add_rule_and_check(p, "b", "baa");
    presentation::add_rule_and_check(p, "c", "abbabababaaababababab");

    auto it = presentation::redundant_rule(p, std::chrono::milliseconds(100));
    REQUIRE(it == p.rules.cend());

    presentation::add_rule_and_check(p, "b", "baa");
    it = presentation::redundant_rule(p, std::chrono::milliseconds(100));
    REQUIRE(it != p.rules.cend());
    REQUIRE(*it == "b");
    REQUIRE(*(it + 1) == "baa");
  }

  LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
                          "014",
                          "redundant_rule (word_type)",
                          "[quick][knuth-bendix]") {
    using literals::        operator""_w;
    auto                    rg = ReportGuard(REPORT);
    Presentation<word_type> p;
    p.alphabet(3);
    presentation::add_rule_and_check(p, 0_w, 011_w);
    presentation::add_rule_and_check(p, 1_w, 100_w);
    presentation::add_rule_and_check(p, 2_w, 011010101000101010101_w);

    auto it = presentation::redundant_rule(p, std::chrono::milliseconds(10));
    REQUIRE(it == p.rules.cend());

    presentation::add_rule_and_check(p, 1_w, 100_w);
    it = presentation::redundant_rule(p, std::chrono::milliseconds(10));
    REQUIRE(it != p.rules.cend());
    REQUIRE(*it == 1_w);
    REQUIRE(*(it + 1) == 100_w);
  }

  ////////////////////////////////////////////////////////////////////////
  // Commented out test cases
  ////////////////////////////////////////////////////////////////////////

  // This example verifies the nilpotence of the group using the Sims
  // algorithm. The original presentation was <a,b| [b,a,b], [b,a,a,a,a],
  // [b,a,a,a,b,a,a] >. (where [] mean left-normed commutators). The
  // presentation here was derived by first applying the NQA to find the
  // maximal nilpotent quotient, and then introducing new generators for
  // the PCP generators. It is essential for success that reasonably low
  // values of the maxstoredlen parameter are given.
  // LIBSEMIGROUPS_TEST_CASE(
  //     "KnuthBendix",
  //     "013",
  //     "(from kbmag/standalone/kb_data/verifynilp)",
  //     "[quick][knuth-bendix][kbmag][recursive]") {}
  //   KnuthBendix kb(new RECURSIVE(), "hHgGfFyYdDcCbBaA");
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "DAda", "y");
  //   presentation::add_rule(p, "YByb", "f");
  //   presentation::add_rule(p, "FAfa", "g");
  //   presentation::add_rule(p, "ga", "ag");
  //   presentation::add_rule(p, "GBgb", "h");
  //   presentation::add_rule(p, "cb", "bc");
  //   presentation::add_rule(p, "ya", "ay");
  //   auto rg = ReportGuard(REPORT);
  //
  //   REQUIRE(kb.confluent());
  //
  //   kb.run();
  //   REQUIRE(kb.confluent());
  //   REQUIRE(kb.number_of_active_rules() == 9);
  //
  //   REQUIRE(kb.equal_to("BAba", "c"));
  //   REQUIRE(kb.equal_to("CAca", "d"));
  //   REQUIRE(kb.equal_to("DAda", "y"));
  //   REQUIRE(kb.equal_to("YByb", "f"));
  //   REQUIRE(kb.equal_to("FAfa", "g"));
  //   REQUIRE(kb.equal_to("ga", "ag"));
  //   REQUIRE(kb.equal_to("GBgb", "h"));
  //   REQUIRE(kb.equal_to("cb", "bc"));
  //   REQUIRE(kb.equal_to("ya", "ay"));
  // REQUIRE(kb.active_rules() == std::vector<std::pair<std::string,
  // std::string>>({}));
  // }

  // TODO(later): temporarily commented out to because of change to
  // FpSemigroupInterface that forbids adding rules after started(), and
  // because the copy constructors for KnuthBendix et al. don't currently
  // work LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "014",
  //                         "(cong) finite transformation semigroup "
  //                         "congruence (21 classes)",
  //                         "[quick][congruence][knuth-bendix][cong]") {
  //   auto rg      = ReportGuard(REPORT);
  //   using Transf = LeastTransf<5>;
  //   FroidurePin<Transf> S({Transf({1, 3, 4, 2, 3}), Transf({3, 2, 1, 3,
  //   3})});

  //   REQUIRE(S.size() == 88);
  //   REQUIRE(S.number_of_rules() == 18);

  //   KnuthBendix kb(S);
  //   auto&       P = kb.quotient_froidure_pin();
  //   REQUIRE(P.size() == 88);
  //   kb.add_pair(S.factorisation(Transf({3, 4, 4, 4, 4})),
  //               S.factorisation(Transf({3, 1, 3, 3, 3})));
  //   // P is now invalid, it's a reference to something that was deleted
  //   in
  //   // kb.

  //   REQUIRE(kb.number_of_classes() == 21);
  //   REQUIRE(kb.number_of_classes() == 21);
  //   auto& Q = kb.quotient_froidure_pin();  // quotient

  //   REQUIRE(Q.size() == 21);
  //   REQUIRE(Q.number_of_idempotents() == 3);

  //   std::vector<word_type>
  //   v(static_cast<FroidurePin<detail::KBE>&>(Q).cbegin(),
  //                            static_cast<FroidurePin<detail::KBE>&>(Q).cend());
  //   REQUIRE(v
  //           == std::vector<word_type>({{0},
  //                                      {1},
  //                                      {0, 0},
  //                                      {0, 1},
  //                                      {1, 0},
  //                                      {1, 1},
  //                                      {0, 0, 0},
  //                                      {0, 0, 1},
  //                                      {0, 1, 0},
  //                                      {0, 1, 1},
  //                                      {1, 0, 0},
  //                                      {1, 1, 0},
  //                                      {0, 0, 0, 0},
  //                                      {0, 1, 0, 0},
  //                                      {0, 1, 1, 0},
  //                                      {1, 0, 0, 0},
  //                                      {1, 1, 0, 0},
  //                                      {0, 1, 0, 0, 0},
  //                                      {0, 1, 1, 0, 0},
  //                                      {1, 1, 0, 0, 0},
  //                                      {0, 1, 1, 0, 0, 0}}));

  //   REQUIRE(
  //       kb.word_to_class_index(S.factorisation(Transf({1, 3, 1, 3,
  //       3})))
  //       == kb.word_to_class_index(S.factorisation(Transf({4, 2, 4, 4,
  //       2}))));

  //   REQUIRE(kb.number_of_non_trivial_classes() == 1);
  //   REQUIRE(kb.number_of_generators() == 2);
  //   REQUIRE(kb.cbegin_ntc()->size() == 68);
  // }

  //  A nonhopfian group
  // LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "015",
  //                         "(from kbmag/standalone/kb_data/nonhopf)",
  //                         "[quick][knuth-bendix][kbmag][recursive]") {
  //   KnuthBendix kb(new RECURSIVE(), "aAbB");
  //   presentation::add_rule(p, "Baab", "aaa");
  //   auto rg = ReportGuard(REPORT);

  //   REQUIRE(kb.confluent());

  //   kb.run();
  //   REQUIRE(kb.confluent());
  //   REQUIRE(kb.number_of_active_rules() == 1);

  //   REQUIRE(kb.equal_to("Baab", "aaa"));
  //   REQUIRE(kb.active_rules()
  //           == std::vector<rule_type>({}));
  // }

  // LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "016",
  //                         "(from kbmag/standalone/kb_data/freenilpc3)",
  //                         "[quick][knuth-bendix][kbmag][recursive]") {
  //   KnuthBendix kb(new RECURSIVE(), "yYdDcCbBaA");
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "CBcb", "y");
  //   presentation::add_rule(p, "da", "ad");
  //   presentation::add_rule(p, "ya", "ay");
  //   presentation::add_rule(p, "db", "bd");
  //   presentation::add_rule(p, "yb", "by");
  //   auto rg = ReportGuard(REPORT);

  //   REQUIRE(kb.confluent());

  //   kb.run();
  //   REQUIRE(kb.confluent());
  //   REQUIRE(kb.number_of_active_rules() == 7);

  //   REQUIRE(kb.equal_to("BAba", "c"));
  //   REQUIRE(kb.equal_to("CAca", "d"));
  //   REQUIRE(kb.equal_to("CBcb", "y"));
  //   REQUIRE(kb.equal_to("da", "ad"));
  //   REQUIRE(kb.equal_to("ya", "ay"));
  //   REQUIRE(kb.equal_to("db", "bd"));
  //   REQUIRE(kb.equal_to("yb", "by"));
  //   REQUIRE(kb.active_rules()
  //           == std::vector<rule_type>({}));
  // }

  // TODO(later): temporarily commented out to because of change to
  // FpSemigroupInterface that forbids adding rules after started(), and
  // because the copy constructors for KnuthBendix et al. don't currently
  // work LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "017",
  //                         "add_rule after knuth_bendix",
  //                         "[quick][knuth-bendix]") {
  //   auto        rg = ReportGuard(REPORT);
  //   KnuthBendix kb;
  //   Presentation<std::string> p;
  // //p.alphabet("Bab");
  //   presentation::add_rule(p, "aa", "");
  //   presentation::add_rule(p, "bB", "");
  //   presentation::add_rule(p, "bbb", "");
  //   presentation::add_rule(p, "ababab", "");

  //   REQUIRE(!kb.confluent());
  //   kb.run_for(FOREVER);
  //   REQUIRE(kb.finished());
  //   // The next line tests what happens when run_for is called when
  //   finished. kb.run_for(FOREVER); REQUIRE(kb.number_of_active_rules()
  //   == 11); REQUIRE(kb.confluent()); REQUIRE(kb.size() == 12);

  //   REQUIRE(kb.equal_to("aa", ""));
  //   REQUIRE(!kb.equal_to("a", "b"));

  //   KnuthBendix kb2(&kb);
  //   REQUIRE(kb2.number_of_active_rules() == 11);
  //   kb2.add_rule("a", "b");
  //   REQUIRE(kb2.number_of_rules() == 5);
  //   // Adding a rule does not change the number of active rules until
  //   *after*
  //   // kb.run() is called again.
  //   REQUIRE(kb2.number_of_active_rules() == 11);

  //   using rules_type = std::vector<rule_type>;

  //   REQUIRE(rules_type(kb2.cbegin_rules(), kb2.cend_rules())
  //           == rules_type({{"aa", ""},
  //                          {"bB", ""},
  //                          {"bbb", ""},
  //                          {"ababab", ""},
  //                          {"a", "b"}}));

  //   REQUIRE(!kb2.confluent());
  //   REQUIRE(kb2.size() == 1);
  //   REQUIRE(kb2.confluent());
  //   REQUIRE(kb2.number_of_active_rules() == 3);
  //   REQUIRE(kb2.active_rules() == rules_type({{"B", ""}, {"a", ""},
  //   {"b", "a"}}));
  // }

  // Free nilpotent group of rank 2 and class 2
  // LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "018",
  //                         "(from kbmag/standalone/kb_data/nilp2)",
  //                         "[quick][knuth-bendix][kbmag][recursive]") {
  //   KnuthBendix kb(new RECURSIVE(), "cCbBaA");
  //   presentation::add_rule(p, "ba", "abc");
  //   presentation::add_rule(p, "ca", "ac");
  //   presentation::add_rule(p, "cb", "bc");
  //   auto rg = ReportGuard(REPORT);
  //
  //   REQUIRE(kb.confluent());
  //
  //   kb.run();
  //   REQUIRE(kb.confluent());
  //
  //   REQUIRE(kb.number_of_active_rules() == 3);
  // }

  // monoid presentation of F(2,7) - should produce a monoid of length 30
  // which is the same as the group, together with the empty word. This is
  // a very difficult calculation indeed, however.
  //
  // KBMAG does not terminate when SHORTLEX order is used.
  // LIBSEMIGROUPS_TEST_CASE("KnuthBendix",
  //                         "019",
  //                         "(from kbmag/standalone/kb_data/f27monoid)",
  //                         "[fail][knuth-bendix][kbmag][recursive]") {
  //   KnuthBendix kb(new RECURSIVE(), "abcdefg");
  //   presentation::add_rule(p, "ab", "c");
  //   presentation::add_rule(p, "bc", "d");
  //   presentation::add_rule(p, "cd", "e");
  //   presentation::add_rule(p, "de", "f");
  //   presentation::add_rule(p, "ef", "g");
  //   presentation::add_rule(p, "fg", "a");
  //   presentation::add_rule(p, "ga", "b");
  //   auto rg = ReportGuard(REPORT);

  //   REQUIRE(!kb.confluent());

  //   kb.run();
  //   REQUIRE(kb.confluent());
  //   REQUIRE(kb.number_of_active_rules() == 32767);
  // }

  // This example verifies the nilpotence of the group using the Sims
  // algorithm. The original presentation was <a,b| [b,a,a,a],
  // [b^-1,a,a,a], [a,b,b,b], [a^-1,b,b,b], [a,a*b,a*b,a*b],
  // [a^-1,a*b,a*b,a*b] >. (where [] mean left-normed commutators. The
  // presentation here was derived by first applying the NQA to find the
  // maximal nilpotent quotient, and then introducing new generators for
  // the PCP generators. LIBSEMIGROUPS_TEST_CASE(
  //     "KnuthBendix",
  //     "020",
  //     "(from kbmag/standalone/kb_data/heinnilp)",
  //     "[fail][knuth-bendix][kbmag][recursive]") {
  //   // TODO(later) fails because internal_rewrite expect rules to be
  //   length reducing KnuthBendix kb(new RECURSIVE(), "fFyYdDcCbBaA");
  //   presentation::add_rule(p, "BAba", "c");
  //   presentation::add_rule(p, "CAca", "d");
  //   presentation::add_rule(p, "CBcb", "y");
  //   presentation::add_rule(p, "DBdb", "f");
  //   presentation::add_rule(p, "cBCb", "bcBC");
  //   presentation::add_rule(p, "babABaBA", "abABaBAb");
  //   presentation::add_rule(p, "cBACab", "abcBAC");
  //   presentation::add_rule(p, "BabABBAbab", "aabABBAb");
  //   auto rg = ReportGuard(REPORT);

  //   REQUIRE(!kb.confluent());

  //   kb.run();
  //   REQUIRE(kb.confluent());
  //   REQUIRE(kb.number_of_active_rules() == 32767);
  //  }

}  // namespace libsemigroups
