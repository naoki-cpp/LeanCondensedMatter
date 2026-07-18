import LeanCondensedMatter.SecondQuantization.Common.Statistics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.GroupTheory.Perm.Fin

set_option linter.style.header false

/-!
# Pairings for the finite-temperature Bloch--de Dominicis theorem

The target of this project is the finite-temperature Bloch--de Dominicis factorization of thermal
expectations, not the vacuum-expectation Wick theorem.  The namespace and module name make that
distinction explicit even though the finite pairing combinatorics itself does not depend on a
temperature parameter.

A perfect pairing of `Fin (2 * n)` is represented by its partner permutation: a fixed-point-free
involution.  Mathlib supplies finite permutations but no naturally suitable bundled perfect-pairing
type with the linear order needed for crossing signs, so this file owns only that small predicate.
This representation enumerates `(2 * n)!` permutations and filters the valid ones, instead of
enumerating the powerset of all possible ordered pairs.  It also gives the later Bloch--de Dominicis
induction direct access to the unique partner of every operator position.

Each partner orbit is normalized to `(a, b)` with `a < b`.  Two normalized pairs cross when
`a < c < b < d`, and the statistics-dependent weight is `ζ ^ crossingCount`, where `ζ = +1` for
bosons and `ζ = -1` for fermions.  At four positions the adjacent, crossing, and nested pairings
have weights `1`, `ζ`, and `1`, respectively.

This file is purely combinatorial.  It defines neither operator-valued time ordering, thermal
contractions, thermal expectations, nor the Bloch--de Dominicis factorization theorem itself, and
it imports neither statistics-specific implementation directory.
-/

namespace SecondQuantization
namespace Common
namespace BlochDeDominicis

/-- A permutation represents a perfect pairing when it is involutive and has no fixed point. -/
def IsPairing {n : ℕ} (partner : Equiv.Perm (Fin (2 * n))) : Prop :=
  Function.Involutive partner ∧ ∀ i, partner i ≠ i

instance decidableIsPairing {n : ℕ} (partner : Equiv.Perm (Fin (2 * n))) :
    Decidable (IsPairing partner) :=
  inferInstanceAs (Decidable (
    (∀ i, partner (partner i) = i) ∧ ∀ i, partner i ≠ i))

/-- A perfect pairing of the ordered positions `Fin (2 * n)`, represented by its unique-partner
permutation. -/
abbrev Pairing (n : ℕ) := {partner : Equiv.Perm (Fin (2 * n)) // IsPairing partner}

instance (n : ℕ) : Fintype (Pairing n) := Subtype.fintype IsPairing

instance (n : ℕ) : DecidableEq (Pairing n) := inferInstance

/-- The finite enumeration of all perfect pairings of `Fin (2 * n)`. -/
def allPairings (n : ℕ) : Finset (Pairing n) := Finset.univ

@[simp]
theorem mem_allPairings (pairing : Pairing n) : pairing ∈ allPairings n := by
  simp [allPairings]

/-- The normalized ordered pairs `(i, partner i)` with `i < partner i`, one per partner orbit. -/
def Pairing.pairs {n : ℕ} (pairing : Pairing n) :
    Finset (Fin (2 * n) × Fin (2 * n)) :=
  ((Finset.univ : Finset (Fin (2 * n))).filter fun i => i < pairing.1 i).image fun i =>
    (i, pairing.1 i)

/-- Every pair emitted by `Pairing.pairs` is normalized. -/
theorem Pairing.pairs_normalized {n : ℕ} (pairing : Pairing n)
    {pair : Fin (2 * n) × Fin (2 * n)} (hpair : pair ∈ pairing.pairs) :
    pair.1 < pair.2 := by
  rcases Finset.mem_image.mp hpair with ⟨i, hi, rfl⟩
  exact (Finset.mem_filter.mp hi).2

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def Crosses {n : ℕ} (left right : Fin (2 * n) × Fin (2 * n)) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance decidableCrosses {n : ℕ}
    (left right : Fin (2 * n) × Fin (2 * n)) : Decidable (Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

/-- The number of geometric crossings.  `Crosses` fixes the order of the left endpoints, so each
crossing is counted exactly once. -/
def Pairing.crossingCount {n : ℕ} (pairing : Pairing n) : ℕ :=
  ((pairing.pairs.product pairing.pairs).filter fun pairPair =>
    Crosses pairPair.1 pairPair.2).card

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

/-- The adjacent four-position pairing `(0,1)(2,3)`. -/
def pairingAdjacent : Pairing 2 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩

/-- The crossing four-position pairing `(0,2)(1,3)`. -/
def pairingCrossing : Pairing 2 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩

/-- The nested four-position pairing `(0,3)(1,2)`. -/
def pairingNested : Pairing 2 :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide⟩

/-- There are exactly three perfect pairings of four ordered positions, stated as a `Finset`
equality so the result is independent of any enumeration order. -/
theorem allPairings_two :
    allPairings 2 = {pairingAdjacent, pairingCrossing, pairingNested} := by
  decide

@[simp]
theorem crossingCount_pairingAdjacent : pairingAdjacent.crossingCount = 0 := by
  decide

@[simp]
theorem crossingCount_pairingCrossing : pairingCrossing.crossingCount = 1 := by
  decide

@[simp]
theorem crossingCount_pairingNested : pairingNested.crossingCount = 0 := by
  decide

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
