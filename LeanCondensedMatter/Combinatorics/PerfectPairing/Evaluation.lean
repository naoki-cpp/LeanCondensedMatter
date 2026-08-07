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
endpoints. The evaluator is reducible because it is only notation for the underlying finite product,
and downstream factorization proofs intentionally expose that product. -/
abbrev evaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) : R :=
  weight * ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2

/-- Pairing evaluation depends only on the supplied global weight and the pair kernel on pairs that
actually occur in the pairing. -/
theorem evaluation_congr {n : ℕ} (pairing : Pairing n)
    {weight₁ weight₂ : R}
    {pairValue₁ pairValue₂ : Fin (2 * n) → Fin (2 * n) → R}
    (hweight : weight₁ = weight₂)
    (hpair : ∀ pr ∈ pairing.pairs,
      pairValue₁ pr.1 pr.2 = pairValue₂ pr.1 pr.2) :
    pairing.evaluation weight₁ pairValue₁ = pairing.evaluation weight₂ pairValue₂ := by
  subst weight₂
  apply congrArg (fun x => weight₁ * x)
  exact Finset.prod_congr rfl hpair

@[simp]
theorem evaluation_one (pairing : Pairing n)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) :
    pairing.evaluation 1 pairValue = ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2 := by
  simp [evaluation]

end Pairing
end Combinatorics
