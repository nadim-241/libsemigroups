//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2022 James D. Mitchell
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

// This file contains a declaration of a class for performing the "low-index
// congruence" algorithm for 1-sided congruences of semigroups and monoids.

// TODO(Sims1):
// * implement joins (HopcroftKarp), meets (not sure), containment (find join
//   and check equality)?
// * generating pairs for congruences defined by "word_graph"?
// * is 2-sided congruence method. One approach would be to compute the kernel
//   of the associated homomorphism, which is the largest 2-sided congruence
//   contained in the right congruence. Not sure if this is a good approach.
// * a version which allows specifying the word_graph to Sims1 too
//
// Notes:
// 1. In 2022, when first writing this file, JDM tried templating the word_type
//    used by the presentations in Sims1 (so that we could use StaticVector1
//    for example, using smaller integer types for letters, and the stack to
//    hold the words rather than the heap), but this didn't seem to give any
//    performance improvement, and so I backed out the changes.

#ifndef LIBSEMIGROUPS_SIMS1_HPP_
#define LIBSEMIGROUPS_SIMS1_HPP_

#include <algorithm>   // for max
#include <chrono>      // for high_resolution_clock
#include <cstddef>     // for size_t
#include <cstdint>     // for uint64_t, uint32_t
#include <functional>  // for function
#include <iostream>    // for ostream
#include <iterator>    // for forward_iterator_tag
#include <mutex>       // for mutex
#include <string>      // for operator+, basic_string
#include <thread>      // for thread, yield
#include <utility>     // for move
#include <vector>      // for vector

#include "constants.hpp"        // for UNDEFINED
#include "debug.hpp"            // for LIBSEMIGROUPS_ASSERT
#include "exception.hpp"        // for LIBSEMIGROUPS_EXCEPTION
#include "felsch-graph.hpp"     // for FelschGraph
#include "froidure-pin.hpp"     // for FroidurePin
#include "presentation.hpp"     // for Presentation, Presentati...
#include "to-froidure-pin.hpp"  // for make
#include "to-presentation.hpp"  // for make
#include "transf.hpp"           // for Transf
#include "types.hpp"            // for word_type, congruence_kind
#include "word-graph.hpp"       // for WordGraph

#include "detail/report.hpp"  // for REPORT_DEFAULT, Reporter
#include "detail/stl.hpp"     // for JoinThreads
#include "detail/timer.hpp"   // for Timer

namespace libsemigroups {

  //! Defined in ``sims1.hpp``.
  //!
  //! On this page we describe the `Sims1Stats` class. The purpose of this
  //! class is to collect some statistics related to `Sims1` class template.
  //!
  //! \sa \ref Sims1
  class Sims1Stats {
   public:
    // TODO(doc)
    // Not atomic because this is only accessed by report_progress_from_thread
    uint64_t count_last;
    // TODO(doc)
    // Atomic so as to avoid races between report_progress_from_thread and the
    // threads modifying count_last
    std::atomic_uint64_t count_now;

    //! The maximum number of pending definitions.
    //!
    //! A *pending definition* is just an edge that will be defined at some
    //! point in the future in the WordGraph represented by a Sims1
    //! instance at any given moment.
    //!
    //! This member tracks the maximum number of such pending definitions that
    //! occur during the running of the algorithms in Sims1.
    std::atomic_uint64_t max_pending;

    //! The total number of pending definitions.
    //!
    //! A *pending definition* is just an edge that will be defined at some
    //! point in the future in the WordGraph represented by a Sims1
    //! instance at any given moment.
    //!
    //! This member tracks the total number of pending definitions that
    //! occur during the running of the algorithms in Sims1. This is the same
    //! as the number of nodes in the search tree encounter during the running
    //! of Sims1.
    // Not atomic because this is only accessed by report_progress_from_thread
    uint64_t total_pending_last;

    // TODO(doc)
    // Atomic so as to avoid races between report_progress_from_thread and the
    // threads modifying total_pending_now
    std::atomic_uint64_t total_pending_now;

    Sims1Stats();

    Sims1Stats(Sims1Stats const& that) : Sims1Stats() {
      init_from(that);
    }

    Sims1Stats& operator=(Sims1Stats const& that) {
      return init_from(that);
    }

    Sims1Stats(Sims1Stats&& that) : Sims1Stats() {
      init_from(that);
    }

    Sims1Stats& operator=(Sims1Stats&& that) {
      return init_from(that);
    }

    Sims1Stats& stats_zero();

    Sims1Stats& stats_check_point() {
      count_last         = count_now;
      total_pending_last = total_pending_now;
      return *this;
    }

   private:
    Sims1Stats& init_from(Sims1Stats const& that);
  };

  //! No doc
  // This class allows us to use the same interface for settings for Sims1,
  // RepOrc, and MinimalRepOrc without duplicating the code.
  template <typename Subclass>
  class Sims1Settings {
   protected:
    // These are protected so that Sims1 can reverse them if necessary for
    // left congruences.
    std::vector<word_type>  _exclude;
    std::vector<word_type>  _include;
    Presentation<word_type> _presentation;

   private:
    size_t                                 _idle_thread_restarts;
    std::vector<word_type>::const_iterator _longs_begin;
    size_t                                 _num_threads;
    mutable Sims1Stats                     _stats;

   public:
    // TODO(doc)
    Sims1Settings();

    // TODO(doc)
    // TODO(tests)
    Subclass& init();

    // Copy constructor is explicitly required, the constructor template is not
    // a substitute. If no copy constructor is implemented, then _longs_begin
    // is not properly initialised, and leads to badness.
    Sims1Settings(Sims1Settings const& that) {
      init(that);
    }

    Sims1Settings& operator=(Sims1Settings const& that) {
      init(that);
      return *this;
    }

    //! Construct from Sims1Settings with different subclass.
    template <typename OtherSubclass>
    Sims1Settings(Sims1Settings<OtherSubclass> const& that) {
      init(that);
    }

    template <typename OtherSubclass>
    Sims1Settings& init(Sims1Settings<OtherSubclass> const& that);

    //! Returns the settings object of *this.
    //!
    //! The settings object contains all the settings that are common to
    //! `Sims1`, `RepOrc`, and `MinimalRepOrc`, which are currently:
    //! * \ref presentation
    //! * \ref long_rules
    //! * \ref number_of_threads
    //! * \ref extra
    //!
    //! The return value of this function can be used to
    //! initialise another `Sims1`, `RepOrc`, or
    //! `MinimalRepOrc` with these settings.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns A const reference to `Sims1Settings`.
    //!
    //! \exceptions
    //! \noexcept
    // So that we can access the settings from the derived class T.
    [[nodiscard]] Sims1Settings const& settings() const noexcept {
      return *this;
    }

    //! Copy the settings from \p that into `this`.
    //!
    //! The settings object contains all the settings that are common to
    //! `Sims1`, `RepOrc`, and `MinimalRepOrc`, which are currently:
    //! * \ref presentation
    //! * \ref long_rules
    //! * \ref number_of_threads
    //! * \ref extra
    //!
    //! The return value of this function can be used to initialise another
    //! `Sims1`, `RepOrc`, or `MinimalRepOrc` with these settings.
    //!
    //! \param that the object to copy the settings from.
    //!
    //! \returns A const reference to `this`.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    Subclass& settings_copy_from(Sims1Settings const& that) {
      *this = that;
      return static_cast<Subclass&>(*this);
    }

    //! \anchor number_of_threads
    //! Set the number of threads.
    //!
    //! This function sets the number of threads to be used
    //! by `Sims1`.
    //!
    //! The default value is `1`.
    //!
    //! \param val the maximum number of threads to use.
    //!
    //! \returns A reference to \c this.
    //!
    //! \throws LibsemigroupsException if the argument \p
    //! val is 0.
    //!
    //! \warning If \p val exceeds
    //! `std::thread::hardware_concurrency()`, then this is
    //! likely to have a negative impact on the performance
    //! of the algorithms implemented by `Sims1`.
    Subclass& number_of_threads(size_t val);

    //! Returns the current number of threads.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns
    //! A `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] size_t number_of_threads() const noexcept {
      return _num_threads;
    }

    //! Set the short rules.
    //!
    //! These are the rules used at every node in the depth first search
    //! conducted by `Sims1`.
    //!
    //! If the template parameter \p P is not `Presentation<word_type>`, then
    //! the parameter \p p is first converted to a value of type
    //! `Presentation<word_type>` and it is this converted value that is used.
    //!
    //! \tparam P A specific value of the class template `Presentation`, must
    //! be derived from `PresentationBase`. \param p the presentation.
    //!
    //! \returns A reference to \c this.
    //!
    //! \throws LibsemigroupsException if `to_presentation<word_type>(p)`
    //! throws
    //! \throws LibsemigroupsException if `p` is not valid
    //! \throws LibsemigroupsException if the alphabet of `p` is non-empty and
    //! not equal to that of \ref long_rules or \ref extra. \throws
    //! LibsemigroupsException if `p` has 0-generators and 0-relations.
    template <typename PresentationOfSomeKind>
    Subclass& presentation(PresentationOfSomeKind const& p);

    //! \anchor presentation
    //! Returns a const reference to the current short rules.
    //!
    //! This function returns the defining presentation of
    //! a `Sims1` instance. The congruences computed by
    //! \ref cbegin and \ref cend are defined over the
    //! semigroup or monoid defined by this presentation.
    //!
    //! Note that it might not be the case that the value
    //! returned by this function and the presentation used
    //! to construct the object are the same. A `Sims1`
    //! object requires the generators of the defining
    //! presentation \f$\mathcal{P}\f$ to be \f$\{0,
    //! \ldots, n - 1\}\f$ where \f$n\f$ is the size of the
    //! alphabet of \f$\mathcal{P}\f$. Every occurrence of
    //! every generator \c a in the presentation \c p used
    //! to construct a `Sims1` instance is replaced by
    //! `p.index(a)`.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns
    //! A const reference to `Presentation<word_type>`.
    //!
    //! \exceptions
    //! \noexcept
    //!
    //! \warning
    //! If \ref split_at or \ref long_rule_length have been
    //! called, then some of the defining relations may
    //! have been moved from \ref presentation to \ref
    //! long_rules.
    [[nodiscard]] Presentation<word_type> const& presentation() const noexcept {
      return _presentation;
    }

    //! Set the long rules.
    //!
    //! These are the rules used after a complete deterministic word graph
    //! compatible with \ref presentation has been found by `Sims1`. If such a
    //! word graph is compatible with the long rules specified by this
    //! function, then this word graph is accepted, and if not it is not
    //! accepted.
    //!
    //! If the template parameter \p P is not `Presentation<word_type>`, then
    //! the parameter \p p is first converted to a value of type
    //! `Presentation<word_type>` and it is this converted value that is used.
    //!
    //! \tparam P A specific value of the class template `Presentation`, must
    //! be derived from `PresentationBase`. \param p the presentation.
    //!
    //! \returns A reference to \c this.
    //!
    //! \throws LibsemigroupsException if `to_presentation<word_type>(p)`
    //! throws \throws LibsemigroupsException if `p` is not valid \throws
    //! LibsemigroupsException if the alphabet of `p` is non-empty and not
    //! equal to that of \ref presentation or \ref extra.
    Subclass& cbegin_long_rules(std::vector<word_type>::const_iterator p);

    // TODO(doc)
    Subclass& cbegin_long_rules(size_t pos);

    // TODO(doc)
    Subclass& clear_long_rules() {
      return cbegin_long_rules(_presentation.rules.cend());
    }

    // TODO(doc)
    [[nodiscard]] size_t number_of_long_rules() const noexcept {
      return std::distance(_longs_begin, _presentation.rules.cend()) / 2;
    }

    //! \anchor long_rules
    //! Returns the current long rules.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns
    //! A const reference to `Presentation<word_type>`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] std::vector<word_type>::const_iterator
    cbegin_long_rules() const noexcept {
      LIBSEMIGROUPS_ASSERT(_presentation.rules.cbegin() <= _longs_begin);
      LIBSEMIGROUPS_ASSERT(_longs_begin <= _presentation.rules.cend());
      return _longs_begin;
    }

    //! \anchor extra
    //! Returns a const reference to the additional defining pairs.
    //!
    //! The congruences computed by a Sims1 instance always contain the
    //! relations of this presentation. In other words, the congruences
    //! computed by this instance are only taken among those that contains the
    //! pairs of elements of the underlying semigroup (defined by the
    //! presentation returned by \ref presentation and \ref long_rules)
    //! represented by the relations of the presentation returned by
    //! `extra()`.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns
    //! A const reference to `Presentation<word_type>`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] std::vector<word_type> const& include() const noexcept {
      return _include;
    }

    //! Set the extra rules.
    //!
    //! The congruences computed by a `Sims1` instance always contain the
    //! relations of this presentation. In other words, the congruences
    //! computed by this instance are only taken among those that contains the
    //! pairs of elements of the underlying semigroup (defined by the
    //! presentation returned by \ref presentation and \ref long_rules)
    //! represented by the relations of the presentation returned by
    //! `extra()`.
    //!
    //! If the template parameter \p P is not `Presentation<word_type>`, then
    //! the parameter \p p is first converted to a value of type
    //! `Presentation<word_type>` and it is this converted value that is used.
    //!
    //! \tparam P A specific value of the class template `Presentation`, must
    //! be derived from `PresentationBase`.
    //!
    //! \param p the presentation.
    //!
    //! \returns A reference to \c this.
    //!
    //! \throws LibsemigroupsException if `to_presentation<word_type>(p)`
    //! throws
    //! \throws LibsemigroupsException if `p` is not valid \throws
    //! LibsemigroupsException if the alphabet of `p` is non-empty and not
    //! equal to that of \ref presentation or \ref long_rules.
    template <typename Iterator>
    Subclass& include(Iterator first, Iterator last);

    // TODO(doc)
    Subclass& include(word_type const& lhs, word_type const& rhs);

    // TODO(doc)
    template <typename Container>
    Subclass& include(Container const& c) {
      include(std::begin(c), std::end(c));
      return static_cast<Subclass&>(*this);
    }

    // TODO(doc)
    Subclass& clear_include() {
      _include.clear();
      return static_cast<Subclass&>(*this);
    }

    // TODO(doc)
    template <typename Iterator>
    Subclass& exclude(Iterator first, Iterator last);

    // TODO(doc)
    template <typename Container>
    Subclass& exclude(Container const& c) {
      exclude(std::begin(c), std::end(c));
      return static_cast<Subclass&>(*this);
    }

    // TODO(doc)
    Subclass& exclude(word_type const& lhs, word_type const& rhs);

    // TODO(doc)
    [[nodiscard]] std::vector<word_type> const& exclude() const noexcept {
      return _exclude;
    }

    // TODO(doc)
    Subclass& clear_exclude() {
      _exclude.clear();
      return static_cast<Subclass&>(*this);
    }

    // TODO(Sims1) ranges version of include/exclude?

    //! Returns a const reference to the current stats object.
    //!
    //! The value returned by this function is a `Sims1Stats` object which
    //! contains some statistics related to the current `Sims1` instance and
    //! any part of the depth first search already conducted.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns
    //! A const reference to `Sims1Stats`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] Sims1Stats& stats() const noexcept {
      return _stats;
    }

    //! \anchor long_rule_length
    //! Define the long rule length.
    //!
    //! This function modifies \ref presentation and \ref long_rules so that
    //! \ref presentation only contains those rules whose length (sum of the
    //! lengths of the two sides of the rules) is less than \p val (if any)
    //! and \ref long_rules only contains those rules of length at least \p
    //! val (if any). The rules contained in the union of \ref presentation
    //! and \ref long_rules is invariant under this function, but the
    //! distribution of the rules between \ref presentation and \ref
    //! long_rules is not.
    //!
    //! The relative orders of the rules within \ref presentation and \ref
    //! long_rules may not be preserved.
    //!
    //! \param val the value of the long rule length.
    //!
    //! \returns
    //! A const reference to `this`.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    Subclass& long_rule_length(size_t val);

    // TODO to tpp
    Subclass& idle_thread_restarts(size_t val) {
      if (val == 0) {
        LIBSEMIGROUPS_EXCEPTION(
            "the argument (idle thread restarts) must be non-zero");
      }
      _idle_thread_restarts = val;
      return static_cast<Subclass&>(*this);
    }

    [[nodiscard]] size_t idle_thread_restarts() const noexcept {
      return _idle_thread_restarts;
    }

   protected:
    Subclass const& stats_copy_from(Sims1Stats const& stts) const {
      _stats = std::move(stts);
      return static_cast<Subclass const&>(*this);
    }

    void reverse(std::vector<word_type>& vec) {
      std::for_each(vec.begin(), vec.end(), [](word_type& w) {
        std::reverse(w.begin(), w.end());
      });
    }

   private:
    template <typename OtherSubclass>
    Sims1Settings& init_from(Sims1Settings<OtherSubclass> const& that);
  };

  template <typename Subclass>
  class SimsBase : public Sims1Settings<Subclass>, public Reporter {
   public:
    //! Type for the nodes in the associated WordGraph
    //! objects.
    using node_type  = uint32_t;
    using label_type = typename WordGraph<node_type>::label_type;

    //! Type for letters in the underlying presentation.
    using letter_type = typename word_type::value_type;

    //! The size_type of the associated WordGraph objects.
    using size_type = typename WordGraph<node_type>::size_type;

    // We use WordGraph, even though the iterators produced by this class
    // hold FelschGraph's, none of the features of FelschGraph are useful
    // for the output, only for the implementation
    //! The type of the associated WordGraph objects.
    using word_graph_type = WordGraph<node_type>;

    // using iterator = typename Subclass::iterator;

    SimsBase()                           = default;
    SimsBase(SimsBase const& other)      = default;
    SimsBase(SimsBase&&)                 = default;
    SimsBase& operator=(SimsBase const&) = default;
    SimsBase& operator=(SimsBase&&)      = default;
    ~SimsBase()                          = default;

    Subclass& init() {
      Sims1Settings<Subclass>::init();
      return static_cast<Subclass&>(*this);
    }

    using Sims1Settings<Subclass>::presentation;
    using Sims1Settings<Subclass>::number_of_threads;
    using Sims1Settings<Subclass>::stats;
    using Sims1Settings<Subclass>::include;
    using Sims1Settings<Subclass>::exclude;
    using Sims1Settings<Subclass>::cbegin_long_rules;

    // TODO to tpp
    void report_at_start(size_t num_classes) const {
      std::string num_threads = "0";
      if (number_of_threads() != 1) {
        num_threads = fmt::format("{} / {}",
                                  number_of_threads(),
                                  std::thread::hardware_concurrency());
      }
      auto shortest_short = presentation::shortest_rule_length(presentation());
      auto longest_short  = presentation::longest_rule_length(presentation());

      std::string pairs;
      if (!include().empty() && !exclude().empty()) {
        pairs = fmt::format(", including {} + excluding {} pairs",
                            include().size() / 2,
                            exclude().size() / 2);
      } else if (!include().empty()) {
        pairs = fmt::format(", including {} pairs", include().size() / 2);
      } else if (!exclude().empty()) {
        pairs = fmt::format(", excluding {} pairs", exclude().size() / 2);
      }

      report_no_prefix("{:+<80}\n", "");
      report_default("Sims1: STARTING with {} additional threads . . . \n",
                     num_threads);
      report_no_prefix("{:+<80}\n", "");
      report_default("Sims1: \u2264 {} classes{} for \u27E8A|R\u27E9 with:\n",
                     num_classes,
                     pairs);
      report_default("Sims1: |A| = {}, |R| = {}, "
                     "|u| + |v| \u2208 [{}, {}], \u2211(|u| + |v|) = {}\n",
                     presentation().alphabet().size(),
                     presentation().rules.size() / 2,
                     shortest_short,
                     longest_short,
                     presentation::length(presentation()));

      if (cbegin_long_rules() != presentation().rules.cend()) {
        auto first = presentation().rules.cbegin(), last = cbegin_long_rules();

        report_default("Sims1: {} \"short\" relations with: ",
                       std::distance(first, last) / 2);
        report_no_prefix(
            "|u| + |v| \u2208 [{}, {}] and \u2211(|u| + |v|) = {}\n",
            presentation::shortest_rule_length(first, last),
            presentation::longest_rule_length(first, last),
            presentation::length(first, last));

        first = cbegin_long_rules(), last = presentation().rules.cend();
        report_default("Sims1: {} \"long\" relations with: ",
                       std::distance(first, last) / 2);
        report_no_prefix(
            "|u| + |v| \u2208 [{}, {}] and \u2211(|u| + |v|) = {}\n",
            presentation::shortest_rule_length(first, last),
            presentation::longest_rule_length(first, last),
            presentation::length(first, last));
      }
      Reporter::reset_start_time();
    }

    // TODO to tpp
    void report_progress_from_thread() const {
      using namespace detail;       // NOLINT(build/namespaces)
      using namespace std::chrono;  // NOLINT(build/namespaces)

      auto time_total_ns = delta(start_time());
      auto time_diff     = delta(last_report());

      // Stats
      auto count_now          = stats().count_now.load();
      auto count_diff         = count_now - stats().count_last;
      auto total_pending_now  = stats().total_pending_now.load();
      auto total_pending_diff = total_pending_now - stats().total_pending_last;

      constexpr uint64_t billion = 1'000'000'000;
      uint64_t congs_per_sec = (billion * count_now) / time_total_ns.count();
      uint64_t nodes_per_sec
          = (billion * total_pending_now) / time_total_ns.count();

      nanoseconds time_per_cong_last_sec(0);
      if (count_diff != 0) {
        time_per_cong_last_sec = time_diff / count_diff;
      }

      nanoseconds time_per_node_last_sec(0);
      if (total_pending_diff != 0) {
        time_per_node_last_sec = time_diff / total_pending_diff;
      }

      nanoseconds time_per_cong(0);
      if (count_now != 0) {
        time_per_cong = time_total_ns / count_now;
      }

      nanoseconds time_per_node(0);
      if (total_pending_now != 0) {
        time_per_node = time_total_ns / total_pending_now;
      }

      ReportCell<2> rc;
      rc.min_width(0, 7).min_width(1, 11);
      rc(group_digits,
         "Sims1: total        {} (cong.)   | {} (nodes) \n",
         count_now,
         total_pending_now);

      rc(signed_group_digits,
         "Sims1: diff         {} (cong.)   | {} (nodes)\n",
         count_diff,
         total_pending_diff);

      rc(group_digits,
         "Sims1: mean         {} (cong./s) | {} (node/s)\n",
         congs_per_sec,
         nodes_per_sec);

      rc("Sims1: time last s. {} (/cong.)  | {} (/node)\n",
         string_time(time_per_cong_last_sec),
         string_time(time_per_node_last_sec));

      rc("Sims1: mean time    {} (/cong.)  | {} (/node)\n",
         string_time(time_per_cong),
         string_time(time_per_node));

      rc("Sims1: time         {} (total)   |\n", string_time(time_total_ns));

      reset_last_report();
      stats().stats_check_point();
    }

    // TODO to tpp
    void report_final() const {
      report_progress_from_thread();
      report_no_prefix("{:+<80}\n", "");
      report_default("Sims1: FINISHED!\n");
      report_no_prefix("{:+<80}\n", "");
    }

    // TODO to tpp
    template <typename iterator>
    [[nodiscard]] iterator cbegin(size_type n) const {
      throw_if_not_ready(n);
      return iterator(static_cast<Subclass const*>(this), n);
    }

    // TODO to tpp
    template <typename iterator>
    [[nodiscard]] iterator cend(size_type n) const {
      throw_if_not_ready(n);
      return iterator(static_cast<Subclass const*>(this), 0);
    }

    // TODO to tpp
    // TODO private
    void throw_if_not_ready(size_type n) const {
      if (n == 0) {
        LIBSEMIGROUPS_EXCEPTION("the argument (size_type) must be non-zero");
      } else if (presentation().rules.empty()
                 && presentation().alphabet().empty()) {
        LIBSEMIGROUPS_EXCEPTION("the presentation() must be defined before "
                                "calling this function");
      }
    }

    //     // Apply the function pred to every one-sided congruence with at
    //     // most n classes
    void for_each(size_type                                   n,
                  std::function<void(word_graph_type const&)> pred) const {
      using thread_runner = typename Subclass::thread_runner;
      using iterator      = typename Subclass::iterator;
      throw_if_not_ready(n);

      report_at_start(n);
      if (number_of_threads() == 1) {
        if (!reporting_enabled()) {
          // Don't care about stats in this case
          std::for_each(cbegin<iterator>(n), cend<iterator>(n), pred);
        } else {
          Subclass::stats().stats_zero();
          detail::Ticker t([this]() { report_progress_from_thread(); });
          auto           it   = cbegin<iterator>(n);
          auto const     last = cend<iterator>(n);
          for (; it != last; ++it) {
            pred(*it);
          }
          report_final();
        }
      } else {
        thread_runner den(
            static_cast<Subclass const*>(this), n, number_of_threads());
        auto pred_wrapper = [&pred](word_graph_type const& ad) {
          pred(ad);
          return false;
        };
        if (!reporting_enabled()) {
          den.run(pred_wrapper);
        } else {
          stats().stats_zero();
          detail::Ticker t([this]() { report_progress_from_thread(); });
          den.run(pred_wrapper);
          report_final();
        }
      }
    }

    word_graph_type
    find_if(size_type                                   n,
            std::function<bool(word_graph_type const&)> pred) const {
      using thread_runner = typename Subclass::thread_runner;
      using iterator      = typename Subclass::iterator;
      throw_if_not_ready(n);
      report_at_start(n);
      if (number_of_threads() == 1) {
        if (!reporting_enabled()) {
          return *std::find_if(cbegin<iterator>(n), cend<iterator>(n), pred);
        } else {
          stats().stats_zero();
          detail::Ticker t([this]() { report_progress_from_thread(); });

          auto       it   = cbegin<iterator>(n);
          auto const last = cend<iterator>(n);

          for (; it != last; ++it) {
            if (pred(*it)) {
              report_final();
              return *it;
            }
          }
          report_final();
          return *last;  // the empty digraph
        }
      } else {
        thread_runner den(
            static_cast<Subclass const*>(this), n, number_of_threads());
        if (!reporting_enabled()) {
          den.run(pred);
          return den.word_graph();
        } else {
          stats().stats_zero();
          detail::Ticker t([this]() { report_progress_from_thread(); });
          den.run(pred);
          report_final();
          return den.word_graph();
        }
      }
    }

    // TODO to tpp
    uint64_t number_of_congruences(size_type n) const {
      if (number_of_threads() == 1) {
        uint64_t result = 0;
        for_each(n, [&result](word_graph_type const&) { ++result; });
        return result;
      } else {
        std::atomic_uint64_t result(0);
        for_each(n, [&result](word_graph_type const&) { ++result; });
        return result;
      }
    }
  };

  //! Defined in ``sims1.hpp``.
  //!
  //! On this page we describe the functionality relating to the small index
  //! congruence algorithm. The algorithm implemented by this class template
  //! is essentially the low index subgroup algorithm for finitely presented
  //! groups described in Section 5.6 of [Computation with Finitely Presented
  //! Groups](https://doi.org/10.1017/CBO9780511574702) by C. Sims. The low
  //! index subgroups algorithm was adapted for semigroups and monoids by J.
  //! D. Mitchell and M. Tsalakou.
  //!
  //! The purpose of this class is to provide the functions \ref cbegin, \ref
  //! cend, \ref for_each, and \ref find_if which permit iterating through the
  //! one-sided congruences of a semigroup or monoid defined by a presentation
  //! containing (a possibly empty) set of pairs and with at most a given
  //! number of classes. An iterator returned by \ref cbegin points at an
  //! WordGraph instance containing the action of the semigroup or monoid
  //! on the classes of a congruence.
  class Sims1 : public SimsBase<Sims1> {
   public:
    //! Type for the nodes in the associated WordGraph
    //! objects.
    using node_type  = uint32_t;
    using label_type = typename WordGraph<node_type>::label_type;

    //! Type for letters in the underlying presentation.
    using letter_type = typename word_type::value_type;

    //! The size_type of the associated WordGraph objects.
    using size_type = typename WordGraph<node_type>::size_type;

    // We use WordGraph, even though the iterators produced by this class
    // hold FelschGraph's, none of the features of FelschGraph are useful
    // for the output, only for the implementation
    //! The type of the associated WordGraph objects.
    using word_graph_type = WordGraph<node_type>;

   private:
    congruence_kind _kind;

   public:
    //! Default constructor
    Sims1() = default;

    // TODO(doc)
    Sims1& init() {
      return SimsBase<Sims1>::init();
    }

    //! Construct from \ref congruence_kind.
    //!
    //! \param ck the handedness of the congruences (left or right)
    //!
    //! \throws LibsemigroupsException if \p ck is \ref
    //! congruence_kind::twosided
    //!
    //! \sa \ref cbegin and \ref cend.
    explicit Sims1(congruence_kind ck) : SimsBase<Sims1>(), _kind() {
      kind(ck);
    }

    // TODO(doc)
    template <typename W>
    Sims1(congruence_kind ck, Presentation<W> p) : Sims1(ck) {
      presentation(p);
    }

    //! Default copy constructor.
    Sims1(Sims1 const& other) = default;

    //! Default move constructor.
    Sims1(Sims1&&) = default;

    //! Default copy assignment operator.
    Sims1& operator=(Sims1 const&) = default;

    //! Default move assignment operator.
    Sims1& operator=(Sims1&&) = default;

    // No doc
    ~Sims1() = default;

#ifndef DOXYGEN_SHOULD_SKIP_THIS
    template <typename PresentationOfSomeKind>
    Sims1& presentation(PresentationOfSomeKind const& p) {
      SimsBase<Sims1>::presentation(p);
      if (_kind == congruence_kind::left) {
        presentation::reverse(_presentation);
      }
      return *this;
    }

    // Must accept at least one argument so that we're not calling the 0-arg
    // include() which is const!
    template <typename Arg, typename... Args>
    Sims1& include(Arg arg, Args&&... args) {
      SimsBase<Sims1>::include(arg, std::forward<Args>(args)...);
      if (_kind == congruence_kind::left) {
        SimsBase<Sims1>::reverse(_include);
      }
      return *this;
    }

    // Must accept at least one argument so that we're not calling the 0-arg
    // exclude() which is const!
    template <typename Arg, typename... Args>
    Sims1& exclude(Arg arg, Args&&... args) {
      SimsBase<Sims1>::exclude(arg, std::forward<Args>(args)...);
      if (_kind == congruence_kind::left) {
        SimsBase<Sims1>::reverse(_exclude);
      }
      return *this;
    }

    // This is required because "using SimsBase<Sims1>::include;" tries to
    // drag in all of the include mem fns from SimsBase, which clash with
    // the fns above.
    [[nodiscard]] std::vector<word_type> const& include() const noexcept {
      return SimsBase<Sims1>::include();
    }

    // This is required because "using SimsBase<Sims1>::exclude;" tries to
    // drag in all of the include mem fns from SimsBase, which clash with
    // the fns above.
    [[nodiscard]] std::vector<word_type> const& exclude() const noexcept {
      return SimsBase<Sims1>::exclude();
    }
#endif

    using SimsBase<Sims1>::cbegin_long_rules;
    using SimsBase<Sims1>::number_of_threads;
    using SimsBase<Sims1>::presentation;

    // TODO(doc)
    [[nodiscard]] congruence_kind kind() const noexcept {
      return _kind;
    }

    // TODO(doc)
    Sims1& kind(congruence_kind ck);

   public:
    //! Returns the number of one-sided congruences with up to a given
    //! number of classes.
    //!
    //! This function is similar to `std::distance(begin(n), end(n))` and
    //! exists to:
    //! * provide some feedback on the progress of the computation if it runs
    //!   for more than 1 second.
    //! * allow for the computation of `std::distance(begin(n), end(n))` to be
    //!   performed using \ref number_of_threads in parallel.
    //!
    //! \param n the maximum number of congruence classes.
    //!
    //! \returns A value of type \c uint64_t.
    //!
    //! \throws LibsemigroupsException if \p n is \c 0.
    //! \throws LibsemigroupsException if `presentation()` has 0-generators
    //! and 0-relations (i.e. it has not been initialised).
    using SimsBase<Sims1>::number_of_congruences;

    //! Apply the function \p pred to every one-sided
    //! congruence with at most \p n classes
    //!
    //! This function is similar to
    //! `std::for_each(begin(n), end(n), pred)` and exists
    //! to:
    //! * provide some feedback on the progress of the
    //!   computation if it runs for more than 1 second.
    //! * allow for the computation of
    //!   `std::for_each(begin(n), end(n), pred)` to be
    //!   performed using \ref number_of_threads in parallel.
    //!
    //! \param n the maximum number of congruence classes.
    //! \param pred the predicate applied to every congruence found.
    //!
    //! \returns (None)
    //!
    //! \throws LibsemigroupsException if \p n is \c 0.
    //! \throws LibsemigroupsException if `presentation()` has 0-generators and
    //! 0-relations (i.e. it has not been initialised).
    // void for_each(size_type                                   n,
    //              std::function<void(word_graph_type const&)> pred) const;
    using SimsBase<Sims1>::for_each;

    //! Apply the function \p pred to every one-sided congruence with at most \p
    //! n classes, until it returns \c true.
    //!
    //! This function is similar to `std::find_if(begin(n),
    //! end(n), pred)` and exists to:
    //! * provide some feedback on the progress of the computation if it runs
    //!   for more than 1 second.
    //! * allow for the computation of `std::find_if(begin(n), end(n), pred)`
    //!   to be performed using \ref number_of_threads in parallel.
    //!
    //! \param n the maximum number of congruence classes.
    //! \param pred the predicate applied to every congruence found.
    //!
    //! \returns The first congruence whose WordGraph for which \p pred returns
    //! \c true.
    //!
    //! \throws LibsemigroupsException if \p n is \c 0.
    //! \throws LibsemigroupsException if `presentation()` has 0-generators and
    //! 0-relations (i.e. it has not been initialised).
    using SimsBase<Sims1>::find_if;

   private:
    friend class Sims2;

    struct PendingDef {
      PendingDef() = default;

      PendingDef(node_type   s,
                 letter_type g,
                 node_type   t,
                 size_type   e,
                 size_type   n,
                 bool        tin) noexcept
          : source(s),
            generator(g),
            target(t),
            num_edges(e),
            num_nodes(n),
            target_is_new_node(tin) {}
      node_type   source;
      letter_type generator;
      node_type   target;
      size_type   num_edges;  // Number of edges in the graph when
                              // *this was added to the stack
      size_type num_nodes;    // Number of nodes in the graph
                              // after the definition is made
      bool target_is_new_node;
    };

    // This class collects some common aspects of the iterator and
    // thread_iterator nested classes. The mutex does nothing for <iterator>
    // and is an actual std::mutex for <thread_iterator>. Also subclassed by
    // Sims2::iterator_base.
    //
    // TODO(maybe) template PendingDef so that we can include extra stuff in the
    // 2-sided version if necessary
    //
    // TODO(maybe) also template the subclass so that we don't have to store a
    // Sims1 const* if we are in Sims2
    class iterator_base {
     public:
      //! No doc
      using const_reference =
          typename std::vector<word_graph_type>::const_reference;

      //! No doc
      using const_pointer =
          typename std::vector<word_graph_type>::const_pointer;

     private:
      size_type _max_num_classes;
      size_type _min_target_node;

     protected:
      // TODO(Sims1) ensure that _felsch_graph's settings are
      // properly initialised
      using Definition = std::pair<node_type, label_type>;

      FelschGraph<word_type, node_type, std::vector<Definition>> _felsch_graph;

      // This mutex does nothing for iterator, only does
      // something for thread_iterator
      std::mutex              _mtx;
      std::vector<PendingDef> _pending;
      Sims1 const*            _sims1;

      // Push initial PendingDef's into _pending, see tpp
      // file for explanation.
      void init(size_type n);

      // We could use the copy constructor, but there's no point in copying
      // anything except the FelschGraph and so we only copy that.
      void copy_felsch_graph(iterator_base const& that) {
        _felsch_graph = that._felsch_graph;
      }

      // Try to make the definition represented by PendingDef, returns false if
      // it wasn't possible, and true if it was.
      //! No doc
      [[nodiscard]] bool try_define(PendingDef const&);

      // Try to pop from _pending into the argument (reference), returns true if
      // successful and false if not.
      [[nodiscard]] bool try_pop(PendingDef&);

     public:
      //! No doc
      iterator_base(Sims1 const* s, size_type n);

      // None of the constructors are noexcept because the corresponding
      // constructors for Presentation aren't currently

      //! No doc
      iterator_base() = default;

      //! No doc
      iterator_base(iterator_base const& that);

      //! No doc
      iterator_base(iterator_base&& that);

      //! No doc
      iterator_base& operator=(iterator_base const& that);

      //! No doc
      iterator_base& operator=(iterator_base&& that);

      //! No doc
      ~iterator_base();

      //! No doc
      [[nodiscard]] bool operator==(iterator_base const& that) const noexcept {
        return _felsch_graph == that._felsch_graph;
      }

      //! No doc
      [[nodiscard]] bool operator!=(iterator_base const& that) const noexcept {
        return !(operator==(that));
      }

      //! No doc
      [[nodiscard]] const_reference operator*() const noexcept {
        return _felsch_graph;
      }

      //! No doc
      [[nodiscard]] const_pointer operator->() const noexcept {
        return &_felsch_graph;
      }

      //! No doc
      void swap(iterator_base& that) noexcept;

      //! No doc
      Sims1Stats& stats() noexcept {
        return _sims1->stats();
      }

      size_type maximum_number_of_classes() const noexcept {
        return _max_num_classes;
      }
    };  // class iterator_base

    //! The return type of \ref cbegin and \ref cend.
    //!
    //! This is a forward iterator values of this type are expensive to copy
    //! due to their internal state, and prefix increment should be
    //! preferred to postfix.
    //
    // Has a template parameter because it's also used by Sims2
    template <typename Base>
    class iterator_template : public Base {
      using Base::init;
      using Base::try_define;
      using Base::try_pop;

     public:
      //! No doc
      using const_pointer = typename Base::const_pointer;
      //! No doc
      using const_reference = typename Base::const_reference;

      //! No doc
      using size_type = typename std::vector<word_graph_type>::size_type;
      //! No doc
      using difference_type =
          typename std::vector<word_graph_type>::difference_type;
      //! No doc
      using pointer = typename std::vector<word_graph_type>::pointer;
      //! No doc
      using reference = typename std::vector<word_graph_type>::reference;
      //! No doc
      using value_type = word_graph_type;
      //! No doc
      using iterator_category = std::forward_iterator_tag;

      //! No doc
      using Base::Base;

     private:
      // Only want Sims1 to be able to use this constructor.
      // TODO to tpp
      iterator_template(Sims1 const* s, size_type n) : Base(s, n) {
        if (this->_felsch_graph.number_of_active_nodes() == 0) {
          return;
        }
        init(n);
        ++(*this);
        // The increment above is required so that when dereferencing any
        // instance of this type we obtain a valid word graph (o/w the value
        // pointed to here is empty).
      }

      // So that we can use the constructor above.
      friend iterator_template<iterator_base>
          SimsBase<Sims1>::cbegin(SimsBase::size_type) const;

      friend iterator_template<iterator_base>
          SimsBase::cend(SimsBase::size_type) const;

     public:
      //! No doc
      ~iterator_template() = default;

      // prefix
      //! No doc
      // TODO to tpp
      iterator_template const& operator++() {
        PendingDef current;
        while (try_pop(current)) {
          if (try_define(current)) {
            return *this;
          }
        }
        this->_felsch_graph.number_of_active_nodes(0);
        // indicates that the iterator is done
        this->_felsch_graph.induced_subgraph_no_checks(0, 0);
        return *this;
      }

      // postfix
      //! No doc
      iterator_template operator++(int) {
        iterator_template copy(*this);
        ++(*this);
        return copy;
      }

      using Base::swap;
    };  // class iterator_template

   public:
    using iterator = iterator_template<iterator_base>;

    //! Returns a forward iterator pointing at the first congruence.
    //!
    //! Returns a forward iterator pointing to the WordGraph representing
    //! the first congruence described by Sims1 object with at most \p n
    //! classes.
    //!
    //! If incremented, the iterator will point to the next such congruence.
    //! The order which the congruences are returned in is implementation
    //! specific. Iterators of the type returned by this function are equal
    //! whenever they point to equal objects. The iterator is exhausted if
    //! and only if it points to an WordGraph with zero nodes.
    //!
    //! The meaning of the WordGraph pointed at by Sims1 iterators depends
    //! on whether the input is a monoid presentation (i.e.
    //! Presentation::contains_empty_word() returns \c true) or a semigroup
    //! presentation. If the input is a monoid presentation for a monoid
    //! \f$M\f$, then the WordGraph pointed to by an iterator of this type
    //! has precisely \p n nodes, and the right action of \f$M\f$ on the
    //! nodes of the word graph is isomorphic to the action of \f$M\f$ on the
    //! classes of a right congruence.
    //!
    //! If the input is a semigroup presentation for a semigroup \f$S\f$,
    //! then the WordGraph has \p n + 1 nodes, and the right action of
    //! \f$S\f$ on the nodes \f$\{1, \ldots, n\}\f$ of the WordGraph is
    //! isomorphic to the action of \f$S\f$ on the classes of a right
    //! congruence. It'd probably be better in this case if node \f$0\f$ was
    //! not included in the output WordGraph, but it is required in the
    //! implementation of the low-index congruence algorithm, and to avoid
    //! unnecessary copies, we've left it in for the time being. \param n
    //! the maximum number of classes in a congruence.
    //!
    //! \returns
    //! An iterator \c it of type \c iterator pointing to an WordGraph with
    //! at most \p n nodes.
    //!
    //! \throws LibsemigroupsException if \p n is \c 0.
    //! \throws LibsemigroupsException if `presentation()`
    //! has 0-generators and 0-relations (i.e. it has not
    //! been initialised).
    //!
    //! \warning
    //! Copying iterators of this type is expensive.  As a consequence,
    //! prefix incrementing \c ++it the returned  iterator \c it
    //! significantly cheaper than postfix incrementing \c it++.
    //!
    //! \sa
    //! \ref cend
    // TODO(Sims1) it'd be good to remove node 0 to avoid confusion. This
    // seems complicated however, and so isn't done at present.
    [[nodiscard]] iterator cbegin(size_type n) const {
      return SimsBase::cbegin<iterator>(n);
    }

    //! Returns a forward iterator pointing one beyond the last congruence.
    //!
    //! Returns a forward iterator pointing to the empty WordGraph. If
    //! incremented, the returned iterator remains valid and continues to
    //! point at the empty WordGraph.
    //!
    //! \param n the maximum number of classes in a
    //! congruence.
    //!
    //! \returns
    //! An iterator \c it of type \c iterator pointing to an WordGraph with
    //! at most \p 0 nodes.
    //!
    //! \throws LibsemigroupsException if \p n is \c 0.
    //! \throws LibsemigroupsException if `presentation()` has 0-generators
    //! and 0-relations (i.e. it has not been initialised).
    //!
    //! \warning
    //! Copying iterators of this type is expensive.  As a consequence,
    //! prefix incrementing \c ++it the returned  iterator \c it
    //! significantly cheaper than postfix incrementing \c it++.
    //!
    //! \sa
    //! \ref cbegin
    [[nodiscard]] iterator cend(size_type n) const {
      return SimsBase::cend<iterator>(n);
    }

    class thread_runner;

    // Note that this class is private, and not really an iterator in the usual
    // sense. It is designed solely to work with thread_runner.
    template <typename IteratorBase>
    class thread_iterator : public IteratorBase {
      friend class Sims1::thread_runner;

      using IteratorBase::copy_felsch_graph;

     public:
      //! No doc
      thread_iterator(Sims1 const* s, size_type n) : IteratorBase(s, n) {}

      // None of the constructors are noexcept because the corresponding
      // constructors for std::vector aren't (until C++17).
      //! No doc
      thread_iterator() = delete;
      //! No doc
      thread_iterator(thread_iterator const&) = delete;
      //! No doc
      thread_iterator(thread_iterator&&) = delete;
      //! No doc
      thread_iterator& operator=(thread_iterator const&) = delete;
      //! No doc
      thread_iterator& operator=(thread_iterator&&) = delete;

      //! No doc
      ~thread_iterator() = default;

      using IteratorBase::stats;

     public:
      void push(PendingDef pd) {
        this->_pending.push_back(std::move(pd));
      }

      void steal_from(thread_iterator& that) {
        // WARNING <that> must be locked before calling this function
        std::lock_guard<std::mutex> lock(this->_mtx);
        LIBSEMIGROUPS_ASSERT(this->_pending.empty());
        size_t const n = that._pending.size();
        if (n == 1) {
          return;
        }
        // Copy the FelschGraph from that into *this
        copy_felsch_graph(that);

        // Unzip that._pending into _pending and that._pending, this seems to
        // give better performance in the search than splitting that._pending
        // into [begin, begin + size / 2) and [begin + size / 2, end)
        size_t i = 0;
        for (; i < n - 2; i += 2) {
          this->_pending.push_back(std::move(that._pending[i]));
          that._pending[i / 2] = std::move(that._pending[i + 1]);
        }
        this->_pending.push_back(std::move(that._pending[i]));
        if (i == n - 2) {
          that._pending[i / 2] = std::move(that._pending[i + 1]);
        }

        that._pending.erase(that._pending.cbegin() + that._pending.size() / 2,
                            that._pending.cend());
      }

      bool try_steal(thread_iterator& q) {
        std::lock_guard<std::mutex> lock(this->_mtx);
        if (this->_pending.empty()) {
          return false;
        }
        // Copy the FelschGraph and half pending from *this into q
        q.steal_from(*this);  // Must call steal_from on q, so that q is locked
        return true;
      }
    };

    class thread_runner {
     private:
      std::atomic_bool                                             _done;
      std::vector<std::unique_ptr<thread_iterator<iterator_base>>> _theives;
      std::vector<std::thread>                                     _threads;
      std::mutex                                                   _mtx;
      size_type                                                    _num_threads;
      word_graph_type                                              _result;
      Sims1 const*                                                 _sims1;

      void worker_thread(unsigned                                    my_index,
                         std::function<bool(word_graph_type const&)> hook) {
        PendingDef pd;
        auto const restarts = _sims1->idle_thread_restarts();
        for (size_t i = 0; i < restarts; ++i) {
          while ((pop_from_local_queue(pd, my_index)
                  || pop_from_other_thread_queue(pd, my_index))
                 && !_done) {
            if (_theives[my_index]->try_define(pd)) {
              if (hook(**_theives[my_index])) {
                // hook returns true to indicate that we should stop early
                std::lock_guard<std::mutex> lock(_mtx);
                if (!_done) {
                  _done   = true;
                  _result = **_theives[my_index];
                }
                return;
              }
            }
          }
          std::this_thread::yield();
          // It's possible to reach here before all of the work is done,
          // because by coincidence there's nothing in the local queue and
          // nothing in any other queue either, this sometimes leads to
          // threads shutting down earlier than desirable. On the other hand,
          // maybe this is a desirable.
        }
      }

      bool pop_from_local_queue(PendingDef& pd, unsigned my_index) {
        return _theives[my_index]->try_pop(pd);
      }

      bool pop_from_other_thread_queue(PendingDef& pd, unsigned my_index) {
        for (size_t i = 0; i < _theives.size() - 1; ++i) {
          unsigned const index = (my_index + i + 1) % _theives.size();
          // Could always do something different here, like find
          // the largest queue and steal from that? I tried this and it didn't
          // seem to be faster.
          if (_theives[index]->try_steal(*_theives[my_index])) {
            return pop_from_local_queue(pd, my_index);
          }
        }
        return false;
      }

     public:
      thread_runner(Sims1 const* s, size_type n, size_type num_threads)
          : _done(false),
            _theives(),
            _threads(),
            _mtx(),
            _num_threads(num_threads),
            _result(),
            _sims1(s) {
        for (size_t i = 0; i < _num_threads; ++i) {
          _theives.push_back(
              std::make_unique<thread_iterator<iterator_base>>(s, n));
        }
        _theives.front()->init(n);
      }

      ~thread_runner() = default;

      word_graph_type const& word_graph() const {
        return _result;
      }

      void run(std::function<bool(word_graph_type const&)> hook) {
        try {
          detail::JoinThreads joiner(_threads);
          for (size_t i = 0; i < _num_threads; ++i) {
            _threads.push_back(std::thread(
                &thread_runner::worker_thread, this, i, std::ref(hook)));
          }
        } catch (...) {
          _done = true;
          throw;
        }
      }
    };  // class thread_runner
  };

  //! Defined in ``sims1.hpp``.
  //!
  //! This class is a helper for `Sims1` calling the `word_graph` member
  //! function attempts to find a right congruence, represented as an
  //! WordGraph, of the semigroup or monoid defined by the presentation
  //! consisting of its \ref presentation and \ref long_rules with the
  //! following properties:
  //! * the transformation semigroup defined by the WordGraph has size
  //!   \ref target_size;
  //! * the number of nodes in the WordGraph is at least \ref min_nodes
  //!   and at most \ref max_nodes.
  //!
  //! If no such WordGraph can be found, then an empty WordGraph is
  //! returned (with `0` nodes and `0` edges).
  class RepOrc : public Sims1Settings<RepOrc> {
   private:
    size_t _min;
    size_t _max;
    size_t _size;

   public:
    //! Default constructor.
    RepOrc() : _min(), _max(), _size() {
      init();
    }
    // TODO(doc)
    RepOrc& init();

    //! Construct from Sims1 or MinimalRepOrc.
    //!
    //! This constructor creates a new RepOrc instance with
    //! the same Sims1Settings as \p s but that is
    //! otherwise uninitialised.
    //!
    //! \tparam S the type of the argument \p s (which is
    //! derived from `Sims1Settings<S>`).
    //!
    //! \param s the Sims1 or MinimalRepOrc whose settings
    //! should be used.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    template <typename OtherSubclass>
    explicit RepOrc(Sims1Settings<OtherSubclass> const& s) : RepOrc() {
      Sims1Settings<RepOrc>::init(s);
    }

    template <typename OtherSubclass>
    RepOrc& init(Sims1Settings<OtherSubclass> const& s) {
      Sims1Settings<RepOrc>::init(s);
      return *this;
    }

    //! Set the minimum number of nodes.
    //!
    //! This function sets the minimal number of nodes in
    //! the WordGraph that we are seeking.
    //!
    //! \param val the minimum number of nodes
    //!
    //! \returns A reference to `this`.
    //!
    //! \exceptions
    //! \noexcept
    RepOrc& min_nodes(size_t val) noexcept {
      _min = val;
      return *this;
    }

    //! The current minimum number of nodes.
    //!
    //! This function returns the current value for the
    //! minimum number of nodes in the WordGraph that we
    //! are seeking.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns A value of type `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] size_t min_nodes() const noexcept {
      return _min;
    }

    //! Set the maximum number of nodes.
    //!
    //! This function sets the maximum number of nodes in
    //! the WordGraph that we are seeking.
    //!
    //! \param val the maximum number of nodes
    //!
    //! \returns A reference to `this`.
    //!
    //! \exceptions
    //! \noexcept
    RepOrc& max_nodes(size_t val) noexcept {
      _max = val;
      return *this;
    }

    //! The current maximum number of nodes.
    //!
    //! This function returns the current value for the
    //! maximum number of nodes in the WordGraph that we
    //! are seeking.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns A value of type `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] size_t max_nodes() const noexcept {
      return _max;
    }

    //! Set the target size.
    //!
    //! This function sets the target size, i.e. the
    //! desired size of the transformation semigroup
    //! corresponding to the WordGraph returned by the
    //! function \ref word_graph.
    //!
    //! \param val the target size.
    //!
    //! \returns A reference to `this`.
    //!
    //! \exceptions
    //! \noexcept
    RepOrc& target_size(size_t val) noexcept {
      _size = val;
      return *this;
    }

    //! The current target size.
    //!
    //! This function returns the current value for the
    //! target size, i.e. the desired size of the
    //! transformation semigroup corresponding to the
    //! WordGraph returned by the function \ref word_graph.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns A value of type `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] size_t target_size() const noexcept {
      return _size;
    }

    //! Get the word_graph.
    //!
    //! This function attempts to find a right congruence,
    //! represented as an WordGraph, of the semigroup or
    //! monoid defined by the presentation consisting of
    //! its \ref presentation and \ref long_rules with the
    //! following properties:
    //! * the transformation semigroup defined by the
    //! WordGraph has size \ref target_size;
    //! * the number of nodes in the WordGraph is at least
    //! \ref min_nodes
    //!   and at most \ref max_nodes.
    //!
    //! If no such WordGraph can be found, then an empty
    //! WordGraph is returned (with `0` nodes and `0`
    //! edges).
    //!
    //! \warning The return value of this function is
    //! recomputed every time it is called.
    //!
    //! \warning If the return value of \ref
    //! number_of_threads is greater than \c 1, then the
    //! value returned by this function is
    //! non-deterministic, and may vary even for the same
    //! parameters.
    //!
    //! \tparam T the type of the nodes in the returned
    //! word graph. \param (None) this function has no
    //! parameters.
    //!
    //! \returns A value of type `WordGraph`.
    //!
    //! \exceptions \no_libsemigroups_except
    [[nodiscard]] Sims1::word_graph_type word_graph() const;

    using Sims1Settings<RepOrc>::presentation;
    using Sims1Settings<RepOrc>::cbegin_long_rules;
  };

  //! Defined in ``sims1.hpp``.
  //!
  //! This class is a helper for `Sims1`, calling the `word_graph` member
  //! function attempts to find a right congruence, represented as an
  //! WordGraph, with the minimum possible number of nodes such that the
  //! action of the semigroup or monoid defined by the presentation consisting
  //! of its \ref presentation and \ref long_rules on the nodes of the
  //! WordGraph corresponds to a semigroup of size \ref target_size.
  //!
  //! If no such WordGraph can be found, then an empty WordGraph is
  //! returned (with `0` nodes and `0` edges).
  class MinimalRepOrc : public Sims1Settings<MinimalRepOrc> {
   private:
    size_t _size;

   public:
    using Sims1Settings<MinimalRepOrc>::stats;

    //! Default constructor
    MinimalRepOrc() = default;

    MinimalRepOrc& init() {
      _size = 0;
      return *this;
    }

    //! Set the target size.
    //!
    //! This function sets the target size, i.e. the desired size of the
    //! transformation semigroup corresponding to the WordGraph returned by
    //! the function \ref word_graph.
    //!
    //! \param val the target size.
    //!
    //! \returns A reference to `this`.
    //!
    //! \exceptions
    //! \noexcept
    MinimalRepOrc& target_size(size_t val) noexcept {
      _size = val;
      return *this;
    }

    //! The current target size.
    //!
    //! This function returns the current value for the target size, i.e. the
    //! desired size of the transformation semigroup corresponding to the
    //! WordGraph returned by the function \ref word_graph.
    //!
    //! \param (None) this function has no parameters.
    //!
    //! \returns A value of type `size_t`.
    //!
    //! \exceptions
    //! \noexcept
    [[nodiscard]] size_t target_size() const noexcept {
      return _size;
    }

    //! Get the word graph.
    //!
    //! This function attempts to find a right congruence, represented as an
    //! WordGraph, with the minimum possible number of nodes such that the
    //! action of the semigroup or monoid defined by the presentation
    //! consisting of its \ref presentation and \ref long_rules on the nodes
    //! of the WordGraph corresponds to a semigroup of size \ref
    //! target_size.
    //!
    //! If no such WordGraph can be found, then an empty WordGraph is
    //! returned (with `0` nodes and `0` edges).
    //!
    //! The algorithm implemented by this function repeatedly runs:
    //! \code RepOrc(*this)
    //!     .min_nodes(1)
    //!     .max_nodes(best)
    //!     .target_size(target_size())
    //!     .word_graph();
    //! \endcode
    //! where `best` is initially \ref target_size, until the returned
    //! WordGraph is empty, and then the penultimate WordGraph is returned
    //! (if any).
    //!
    //! \warning The return value of this function is recomputed every time
    //! it is called.
    //!
    //! \warning If the return value of \ref number_of_threads is greater
    //! than \c 1, then the value returned by this function is
    //! non-deterministic, and may vary even for the same parameters.
    //!
    //! \param
    //! (None) this function has no parameters.
    //!
    //! \returns A value of type `WordGraph<uint32_t>`.
    //!
    //! \exceptions \no_libsemigroups_except
    [[nodiscard]] Sims1::word_graph_type word_graph() const;
  };

}  // namespace libsemigroups

#include "sims1.tpp"

#endif  // LIBSEMIGROUPS_SIMS1_HPP_
