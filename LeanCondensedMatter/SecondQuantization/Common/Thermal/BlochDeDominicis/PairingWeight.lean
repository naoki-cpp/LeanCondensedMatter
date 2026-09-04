import LeanCondensedMatter.SecondQuantization.Common.Algebra.Statistics
import LeanCondensedMatter.Combinatorics.ExchangeSign
import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Examples.Four
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# The exchange-statistics weight of a Bloch–de Dominicis pairing

`Pairing.lean` is purely combinatorial — `crossingCount`, `eraseZeroPair`, `insertFirstPair`,
`equivSigma` — with no `Statistics`/`ℂ` dependency. This file adds the one physics-facing quantity
built on top of it: the exchange-statistics weight `ζ ^ crossingCount`, where `ζ = +1` for bosons
and `ζ = -1` for fermions (`Statistics.zetaInt`). Splitting this out keeps the pairing
combinatorics reusable independent of the exchange-statistics choice, and isolates the one place a
future general/arbitrary-ring generalization of `Statistics` would need to touch.

At four positions the adjacent, crossing, and nested pairings have weights `1`, `ζ`, and `1`,
respectively (`four_position_pairings_and_weights`) — the sign pattern the four-point Bloch–de
Dominicis formula uses.
-/

namespace Combinatorics

/-- The exchange-statistics weight `ζ ^ crossings` of a Bloch--de Dominicis pairing. -/
noncomputable def Pairing.weight (s : SecondQuantization.Common.Statistics)
    {n : ℕ} (pairing : Pairing n) : ℂ :=
  (s.zetaInt : ℂ) ^ pairing.crossingCount

end Combinatorics

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

open Combinatorics

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
  apply Combinatorics.pow_eq_of_mod_two_eq ?_ h
  cases s <;> norm_num

/-- A finite product of exchange-sign powers is determined by the parity of the sum of its
exponents. This is the Statistics-generic scalar algebra behind component pairing-weight
factorization, independent of any particular diagram representation. -/
theorem zetaInt_pow_eq_prod_of_sum_mod_two_eq (s : Statistics)
    {ι : Type*} [Fintype ι] (globalExponent : ℕ) (localExponent : ι → ℕ)
    (h : globalExponent % 2 = (∑ i, localExponent i) % 2) :
    (s.zetaInt : ℂ) ^ globalExponent =
      ∏ i, (s.zetaInt : ℂ) ^ localExponent i := by
  classical
  calc
    (s.zetaInt : ℂ) ^ globalExponent =
        (s.zetaInt : ℂ) ^ (∑ i, localExponent i) :=
      zetaInt_pow_eq_of_mod_two_eq s h
    _ = ∏ i, (s.zetaInt : ℂ) ^ localExponent i := by
      rw [← Finset.prod_pow_eq_pow_sum]

/-- Pairing weights multiply whenever the global crossing count has the same parity as the sum of
two local crossing counts. This isolates sign factorization from the combinatorial parity proof. -/
theorem Pairing.weight_eq_mul_of_crossingCount_mod_two_eq (s : Statistics)
    {n nLeft nRight : ℕ} (pairing : Pairing n) (left : Pairing nLeft)
    (right : Pairing nRight)
    (h : pairing.crossingCount % 2 =
      (left.crossingCount + right.crossingCount) % 2) :
    pairing.weight s = left.weight s * right.weight s := by
  simp only [Pairing.weight]
  rw [← pow_add]
  exact zetaInt_pow_eq_of_mod_two_eq s h

/-- A finite-family version of `Pairing.weight_eq_mul_of_crossingCount_mod_two_eq`: once the global
crossing count is identified modulo two with the sum of local crossing counts, the global exchange
weight is the product of all local exchange weights. -/
theorem Pairing.weight_eq_prod_of_crossingCount_mod_two_eq (s : Statistics)
    {ι : Type*} [Fintype ι] {n : ℕ} {localSize : ι → ℕ}
    (pairing : Pairing n) (localPairing : (i : ι) → Pairing (localSize i))
    (h : pairing.crossingCount % 2 =
      (∑ i, (localPairing i).crossingCount) % 2) :
    pairing.weight s = ∏ i, (localPairing i).weight s := by
  simpa only [Pairing.weight] using
    zetaInt_pow_eq_prod_of_sum_mod_two_eq s pairing.crossingCount
      (fun i => (localPairing i).crossingCount) h

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
