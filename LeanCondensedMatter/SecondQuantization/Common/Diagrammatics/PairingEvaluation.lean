import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

set_option linter.style.header false

/-!
# Scalar evaluation of perfect pairings

This module separates the scalar evaluation of a perfect pairing from the physical construction of
its pair contractions.  A caller supplies one global pairing weight and a value for each ordered
pair endpoint; the evaluator multiplies the weight by the finite product of pair values.

The definition is statistics- and state-independent.  In particular, it does not know about Gibbs
states, occupation bases, fermionic or bosonic operators, imaginary-time evolution, or integration.
Those layers provide concrete weights and pair kernels downstream.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {R : Type*} [CommMonoid R]

/-- Evaluate a perfect pairing from a global scalar weight and a scalar kernel on its pair
endpoints. -/
def pairingEvaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) : R :=
  weight * ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2

/-- Pairing evaluation depends only on the supplied global weight and the pair kernel on pairs that
actually occur in the pairing. -/
theorem pairingEvaluation_congr {n : ℕ} (pairing : Pairing n)
    {weight₁ weight₂ : R}
    {pairValue₁ pairValue₂ : Fin (2 * n) → Fin (2 * n) → R}
    (hweight : weight₁ = weight₂)
    (hpair : ∀ pr ∈ pairing.pairs,
      pairValue₁ pr.1 pr.2 = pairValue₂ pr.1 pr.2) :
    pairingEvaluation pairing weight₁ pairValue₁ =
      pairingEvaluation pairing weight₂ pairValue₂ := by
  subst weight₂
  apply congrArg (fun x => weight₁ * x)
  exact Finset.prod_congr rfl hpair

@[simp]
theorem pairingEvaluation_one (pairing : Pairing n)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) :
    pairingEvaluation pairing 1 pairValue =
      ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2 := by
  simp [pairingEvaluation]

end Common
end SecondQuantization
