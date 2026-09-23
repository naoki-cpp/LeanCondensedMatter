import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Scalar evaluation of perfect pairings

A perfect pairing can be evaluated in any commutative monoid from one global weight and a value for
each ordered pair endpoint.  This is purely combinatorial: statistics, states, operators, and
integration are supplied by downstream users.
-/

namespace Combinatorics

open scoped BigOperators

namespace Pairing

variable {R : Type*} [CommMonoid R]

/-- Evaluate a perfect pairing from a global scalar weight and a scalar kernel on its pair
endpoints. -/
def evaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) : R :=
  weight * ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2


end Pairing
end Combinatorics
