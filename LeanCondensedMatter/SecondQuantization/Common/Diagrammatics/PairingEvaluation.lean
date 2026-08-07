import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation

set_option linter.style.header false

/-!
# Compatibility bridge for pairing evaluation

The authoritative scalar evaluator now lives at `Combinatorics.Pairing.evaluation`.  This module is
a temporary migration bridge for remaining SecondQuantization call sites and will be deleted as part
of #750.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {R : Type*} [CommMonoid R]

/-- Temporary compatibility name for `Combinatorics.Pairing.evaluation`. -/
abbrev pairingEvaluation {n : ℕ} (pairing : Pairing n) (weight : R)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) : R :=
  pairing.evaluation weight pairValue

/-- Temporary compatibility theorem for `Combinatorics.Pairing.evaluation_congr`. -/
theorem pairingEvaluation_congr {n : ℕ} (pairing : Pairing n)
    {weight₁ weight₂ : R}
    {pairValue₁ pairValue₂ : Fin (2 * n) → Fin (2 * n) → R}
    (hweight : weight₁ = weight₂)
    (hpair : ∀ pr ∈ pairing.pairs,
      pairValue₁ pr.1 pr.2 = pairValue₂ pr.1 pr.2) :
    pairingEvaluation pairing weight₁ pairValue₁ =
      pairingEvaluation pairing weight₂ pairValue₂ :=
  pairing.evaluation_congr hweight hpair

@[simp]
theorem pairingEvaluation_one (pairing : Pairing n)
    (pairValue : Fin (2 * n) → Fin (2 * n) → R) :
    pairingEvaluation pairing 1 pairValue =
      ∏ pr ∈ pairing.pairs, pairValue pr.1 pr.2 :=
  pairing.evaluation_one pairValue

end Common
end SecondQuantization
