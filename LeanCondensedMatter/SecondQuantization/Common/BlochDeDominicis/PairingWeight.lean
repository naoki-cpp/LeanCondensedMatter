import LeanCondensedMatter.SecondQuantization.Common.Statistics
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.Pairing
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# The exchange-statistics weight of a Bloch–de Dominicis pairing

`Pairing.lean` is purely combinatorial — `crossingCount`, `eraseZeroPair`, `insertFirstPair`,
`equivSigma` — with no `Statistics`/`ℂ` dependency. This file adds the one physics-facing quantity
built on top of it: the exchange-statistics weight `ζ ^ crossingCount`, where `ζ = +1` for bosons
and `ζ = -1` for fermions (`Common.Statistics.zetaInt`). Splitting this out keeps the pairing
combinatorics reusable independent of the exchange-statistics choice, and isolates the one place a
future general/arbitrary-ring generalization of `Statistics` would need to touch.

At four positions the adjacent, crossing, and nested pairings have weights `1`, `ζ`, and `1`,
respectively (`four_position_pairings_and_weights`) — the sign pattern the four-point Bloch–de
Dominicis formula uses.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- The exchange-statistics weight `ζ ^ crossings` of a Bloch--de Dominicis pairing. -/
noncomputable def Pairing.weight (s : Statistics) {n : ℕ} (pairing : Pairing n) : ℂ :=
  (s.zetaInt : ℂ) ^ pairing.crossingCount

@[simp]
theorem Pairing.weight_boson {n : ℕ} (pairing : Pairing n) :
    pairing.weight Statistics.boson = 1 := by
  simp [Pairing.weight]

@[simp]
theorem Pairing.weight_fermion {n : ℕ} (pairing : Pairing n) :
    pairing.weight Statistics.fermion = (-1 : ℂ) ^ pairing.crossingCount := by
  simp [Pairing.weight]

/-- For fermions, the Bloch--de Dominicis pairing weight is the crossing-parity sign. -/
theorem Pairing.weight_fermion_eq_ite {n : ℕ} (pairing : Pairing n) :
    pairing.weight Statistics.fermion =
      if Even pairing.crossingCount then 1 else -1 := by
  rw [Pairing.weight_fermion, neg_one_pow_eq_ite]

/-- The exchange sign `ζ` squares to `1`, so a power of `ζ` only depends on the exponent's
parity. -/
theorem zetaInt_pow_eq_of_mod_two_eq (s : Statistics) {a b : ℕ} (h : a % 2 = b % 2) :
    (s.zetaInt : ℂ) ^ a = (s.zetaInt : ℂ) ^ b := by
  cases s
  · simp
  · simp only [Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one]
    rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- The exponent-recurrence version of `crossingsWithFirstPair_mod_two`: since the exchange sign
`ζ` squares to `1`, matching parities give matching powers. -/
theorem Pairing.weight_eraseZeroPair (s : Statistics) {n : ℕ} (pairing : Pairing (n + 1)) :
    pairing.weight s =
      (s.zetaInt : ℂ) ^ pairing.interveningPositionCount * pairing.eraseZeroPair.weight s := by
  rw [Pairing.weight, Pairing.weight, pairing.crossingCount_eraseZeroPair, pow_add, mul_comm]
  congr 1
  exact zetaInt_pow_eq_of_mod_two_eq s pairing.crossingsWithFirstPair_mod_two

/-- Four-position sanity check: the three structural pairings have weights `1`, `ζ`, and `1`.
This is the combinatorial sign pattern used by the four-point Bloch--de Dominicis formula. -/
theorem four_position_pairings_and_weights (s : Statistics) :
    allPairings 2 = {pairingAdjacent, pairingCrossing, pairingNested} ∧
      pairingAdjacent.weight s = 1 ∧
      pairingCrossing.weight s = (s.zetaInt : ℂ) ∧
      pairingNested.weight s = 1 := by
  simp [allPairings_two, Pairing.weight]

end BlochDeDominicis
end Common
end SecondQuantization
