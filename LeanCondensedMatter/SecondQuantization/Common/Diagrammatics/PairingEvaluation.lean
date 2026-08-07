import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Temporary pairing-evaluation migration bridge

The authoritative scalar evaluator is `Combinatorics.Pairing.evaluation`.  The old Common definition
is retained temporarily with its original reducible body so existing factorization proofs keep their
current unfolding boundary while call sites are migrated in #750.  This module will then be deleted;
it is not a second authoritative API.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
open scoped BigOperators

variable {R : Type*} [CommMonoid R]

/-- Temporary migration definition preserving the old proof-level unfolding behavior. -/
def pairingEvaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) : R :=
  weight * ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2

/-- The temporary Common evaluator agrees with the authoritative combinatorics evaluator. -/
theorem pairingEvaluation_eq_evaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) :
    pairingEvaluation pairing weight pairValue = pairing.evaluation weight pairValue :=
  rfl

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
