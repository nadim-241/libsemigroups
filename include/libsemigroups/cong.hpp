//
// libsemigroups - C++ library for semigroups and monoids
// Copyright (C) 2019-2023 James D. Mitchell
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

// This file contains stuff for creating congruence over FroidurePin objects or
// over Presentation objects.

#ifndef LIBSEMIGROUPS_CONG_HPP_
#define LIBSEMIGROUPS_CONG_HPP_

#include <cstddef>  // for size_t
#include <memory>   // for shared_ptr

#include "cong-intf.hpp"
#include "kambites.hpp"      // for Kambites
#include "knuth-bendix.hpp"  // for KnuthBendix
#include "race.hpp"          // for Race
#include "runner.hpp"        // for Runner
#include "to-todd-coxeter.hpp"
#include "todd-coxeter.hpp"  // for ToddCoxeter
#include "types.hpp"         // for word_type

namespace libsemigroups {
  class FroidurePinBase;  // Forward declaration, constructor parameters

  // The purpose of this class in v3 is just to deliver the winner, then that
  // object is used to answer whatever questions.

  //! Defined in ``cong.hpp``.
  //!
  //! On this page we describe the functionality relating to the Congruence
  //! class. This class can be used for computing a congruence over a semigroup
  //! by running every applicable algorithm from ``libsemigroups`` (and some
  //! variants of the same algorithm) in parallel. This class is provided for
  //! convenience, at present it is not very customisable, and lacks some of
  //! the fine grained control offered by the classes implementing individual
  //! algorithms, such as ToddCoxeter and KnuthBendix.
  //!
  //! \sa congruence_kind and tril.
  //! \par Example
  //! \code
  //! FpSemigroup S;
  //! S.set_alphabet(3);
  //! S.set_identity(0);
  //! S.add_rule({1, 2}, {0});
  //! S.is_obviously_infinite();  // false
  //!
  //! Congruence cong(twosided, S);
  //! cong.add_pair({1, 1, 1}, {0});
  //! cong.number_of_classes(); // 3
  //! \endcode
  class Congruence : public CongruenceInterface {
    /////////////////////////////////////////////////////////////////////////
    // Congruence - data - private
    /////////////////////////////////////////////////////////////////////////
    detail::Race _race;
    bool         _initted;

   public:
    //////////////////////////////////////////////////////////////////////////
    // Congruence - constructors - public
    //////////////////////////////////////////////////////////////////////////

    //! Construct from kind (left/right/2-sided) and options.
    //!
    //! Constructs an empty instance of an interface to a congruence of type
    //! specified by the argument.
    //!
    //! \param type the type of the congruence.
    //! \param opt  optionally specify algorithms to be used (defaults to
    //! options::runners::standard).
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa set_number_of_generators and add_pair.
    explicit Congruence(congruence_kind type)
        : CongruenceInterface(type), _race(), _initted(false) {}
    // TODO init

    //! Construct from kind (left/right/2-sided) and FroidurePin.
    //!
    //! Constructs a Congruence over the FroidurePin instance \p S
    //! representing a left/right/2-sided congruence according to \p type.
    //!
    //! \tparam T a class derived from FroidurePinBase.
    //!
    //! \param type whether the congruence is left, right, or 2-sided
    //! \param S  a const reference to the semigroup over which the congruence
    //! is defined.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Linear in  the size of \p S.
    //!
    //! \warning the parameter `T const& S` is copied, this might be expensive,
    //! use a std::shared_ptr to avoid the copy!
    // template <typename T>
    Congruence(congruence_kind type, FroidurePinBase& S);

    //! Construct from kind (left/right/2-sided) and Presentation.
    //!
    //! Constructs a Congruence over the Presentation instance \p p
    //! representing a left/right/2-sided congruence according to \p type.
    //!
    //! \param type whether the congruence is left, right, or 2-sided
    //! \param p  a const reference to the presentation.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    // TODO constructor for rval ref, and init versions
    Congruence(congruence_kind type, Presentation<word_type> const& p);

    // TODO constructor for rval ref, and init versions
    template <typename Word>
    Congruence(congruence_kind type, Presentation<Word> const& p)
        : Congruence(type, to_presentation<word_type>(p)) {}

    ~Congruence() = default;

    //! Deleted.
    // TODO undelete
    Congruence() = delete;

    //! Deleted.
    // TODO undelete
    Congruence(Congruence const&) = delete;

    //! Deleted.
    // TODO undelete
    Congruence& operator=(Congruence const&) = delete;

    //! Deleted.
    // TODO undelete
    Congruence(Congruence&&) = delete;

    //! Deleted.
    // TODO undelete
    Congruence& operator=(Congruence&&) = delete;

    //////////////////////////////////////////////////////////////////////////
    // CongruenceInterface - pure virtual - public
    //////////////////////////////////////////////////////////////////////////

    [[nodiscard]] uint64_t number_of_classes() override {
      run();
      return std::static_pointer_cast<CongruenceInterface>(_race.winner())
          ->number_of_classes();
    }

    [[nodiscard]] bool contains(word_type const& u,
                                word_type const& v) override {
      run();
      return std::static_pointer_cast<CongruenceInterface>(_race.winner())
          ->contains(u, v);
    }

    void validate_word(word_type const&) const override {
      // Do nothing
    }

    //////////////////////////////////////////////////////////////////////////
    // Congruence - member functions - public
    //////////////////////////////////////////////////////////////////////////

    template <typename Thing>
    std::shared_ptr<Thing> get() {
      init();
      return _race.find_runner<Thing>();
    }

    template <typename Thing>
    [[nodiscard]] bool get() {
      return get<Thing>() != nullptr;
    }

    //! Returns the KnuthBendix instance used to compute the congruence (if
    //! any).
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A std::shared_ptr to a KnuthBendix or \c nullptr.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa has_knuth_bendix().
    // TODO remove
    std::shared_ptr<KnuthBendix> knuth_bendix() {
      init();
      return _race.find_runner<KnuthBendix>();
    }

    //! Checks if a KnuthBendix instance is being used to compute
    //! the congruence.
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A value of type `bool`.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa knuth_bendix().
    // TODO remove
    bool has_knuth_bendix() {
      return knuth_bendix() != nullptr;
    }

    //! Returns the ToddCoxeter instance used to compute the
    //! congruence (if any).
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A shared_ptr to a ToddCoxeter or \c nullptr.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa has_todd_coxeter().
    // TODO remove
    std::shared_ptr<ToddCoxeter> todd_coxeter() {
      init();
      return _race.find_runner<ToddCoxeter>();
    }

    //! Returns the Kambites instance used to compute the congruence (if any).
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A shared_ptr to a Kambites or \c nullptr.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa has_kambites().
    // TODO remove
    std::shared_ptr<Kambites<word_type>> kambites() {
      init();
      return _race.find_runner<Kambites<word_type>>();
    }

    //! Checks if a ToddCoxeter instance is being used to compute
    //! the congruence.
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A value to type `bool`.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa todd_coxeter.
    // TODO remove
    bool has_todd_coxeter() {
      return todd_coxeter() != nullptr;
    }

    //! Checks if a Kambites instance is being used to compute
    //! the congruence.
    //!
    //! \parameters
    //! (None)
    //!
    //! \returns A value to type `bool`.
    //!
    //! \exceptions
    //! \no_libsemigroups_except
    //!
    //! \complexity
    //! Constant.
    //!
    //! \sa \ref kambites.
    // TODO remove
    bool has_kambites() {
      return kambites() != nullptr;
    }

    //! Get the current maximum number of threads.
    //!
    //! \returns
    //! A value of type \c size_t.
    //!
    //! \exceptions
    //! \noexcept
    //!
    //! \complexity
    //! Constant.
    //!
    //! \parameters
    //! (None)
    [[nodiscard]] size_t max_threads() const noexcept {
      return _race.max_threads();
    }

    //! Set the maximum number of threads.
    //!
    //! \param val the number of threads.
    //!
    //! \returns A reference to \c this.
    //!
    //! \exceptions
    //! \noexcept
    //!
    //! \complexity
    //! Constant.
    Congruence& max_threads(size_t val) noexcept {
      _race.max_threads(val);
      return *this;
    }

    [[nodiscard]] size_t number_of_runners() const noexcept {
      return _race.number_of_runners();
    }

   private:
    //////////////////////////////////////////////////////////////////////////
    // Congruence - member functions - private
    //////////////////////////////////////////////////////////////////////////

    void init();

    //////////////////////////////////////////////////////////////////////////
    // Runner - pure virtual member functions - private
    //////////////////////////////////////////////////////////////////////////

    void run_impl() override;
    bool finished_impl() const override {
      return _race.finished();
    }
  };

  namespace congruence {
    // TODO should be word_type/string agnostic
    template <typename Range>
    std::vector<std::vector<word_type>> non_trivial_classes(Congruence& cong,
                                                            Range       r) {
      using rx::operator|;
      cong.run();
      if (cong.has_todd_coxeter() && cong.todd_coxeter()->finished()) {
        return ::libsemigroups::todd_coxeter::non_trivial_classes(
            *cong.todd_coxeter(), r);  // TODO add to_words here
      } else if (cong.has_knuth_bendix() && cong.knuth_bendix()->finished()) {
        auto const& p = cong.knuth_bendix()->presentation();
        auto strings  = ::libsemigroups::knuth_bendix::non_trivial_classes(
            *cong.knuth_bendix(), r | to_strings(p.alphabet()));
        std::vector<std::vector<word_type>> result;
        for (auto const& klass : strings) {
          result.push_back(rx::iterator_range(klass.begin(), klass.end())
                           | to_words(p.alphabet()) | rx::to_vector());
        }
        return result;
      }
      // TODO the case when cong.has_kambites()
      LIBSEMIGROUPS_EXCEPTION_V3("Cannot compute the non-trivial classes!");
      return std::vector<std::vector<word_type>>();
    }
  }  // namespace congruence
}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_CONG_HPP_
