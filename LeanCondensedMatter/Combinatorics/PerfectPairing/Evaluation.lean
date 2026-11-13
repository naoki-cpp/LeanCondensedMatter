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


/-- Reindexing a pairing by an equality of pair counts preserves its
evaluation together with the **oriented endpoint kernel**.  The endpoints
are cast back in their original order, rather than assuming the pair
contraction is symmetric under endpoint exchange. -/
theorem evaluation_cast {m n : ℕ} (h : m = n)
    (pairing : Pairing m) (weight : R)
    (pairValue : Fin (2 * m) → Fin (2 * m) → R) :
    (Equiv.cast (congrArg Pairing h) pairing).evaluation weight
        (fun a b =>
          pairValue (finCongr (congrArg (fun k => 2 * k) h.symm) a)
            (finCongr (congrArg (fun k => 2 * k) h.symm) b)) =
      pairing.evaluation weight pairValue := by
  cases h
  rfl

end Pairing
end Combinatorics
