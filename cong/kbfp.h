//
// libsemigroups - C++ library for computing with semigroups and monoids
// Copyright (C) 2017 James D. Mitchell
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

// This file contains the declaration for the private inner class of Congruence
// called KBFP, which is a subclass of Congruence::DATA.  This class is for
// performing Knuth-Bendix followed by the Froidure-Pin algorithm on the
// quotient.

#ifndef LIBSEMIGROUPS_CONG_KBFP_H_
#define LIBSEMIGROUPS_CONG_KBFP_H_

#include "../cong.h"
#include "../rws.h"
#include "../semigroups.h"

namespace libsemigroups {

  // Knuth-Bendix followed by Froidure-Pin
  class Congruence::KBFP : public Congruence::DATA {
   public:
    explicit KBFP(Congruence& cong)
        : DATA(cong), _rws(new RWS()), _semigroup(nullptr) {}

    ~KBFP() {
      delete _rws;
      delete _semigroup;
    }

    void run() final;

    bool is_done() const final {
      return (_semigroup != nullptr && _semigroup->is_done());
    }

    size_t nr_classes() final {
      assert(is_done());
      return _semigroup->size();
    }

    class_index_t word_to_class_index(word_t const& word) final;

    void compress() override {
      _rws->compress();
    }

   private:
    RWS*       _rws;
    Semigroup* _semigroup;
  };
}  // namespace libsemigroups

#endif  // LIBSEMIGROUPS_CONG_KBFP_H_
