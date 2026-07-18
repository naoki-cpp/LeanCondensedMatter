import LeanCondensedMatter.SecondQuantization.Common.Statistics
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets

set_option linter.style.header false

/-!
# Wick pairings and exchange-statistics weights

The combinatorial input to the finite-mode Wick/Bloch--de Dominicis theorem is a perfect pairing
of the ordered operator positions `Fin (2 * n)`.  Mathlib's perfect-matching API is formulated for
subgraphs of general simple graphs.  That representation is substantially more general than is
needed here and does not retain the canonical linear order used to define Wick crossing signs.
This file therefore uses the smallest ordered representation needed by the later induction: a
finite set of normalized pairs `(a, b)` with `a < b`, in which every position occurs exactly once.

For normalized pairs `(a, b)` and `(c, d)`, the first crosses the second when
`a < c < b < d`.  Counting only this orientation counts every geometric crossing exactly once.
The statistics-dependent pairing weight is

`ζ ^ crossingCount`,

where `ζ = +1` for bosons and `ζ = -1` for fermions.  The explicit four-position result records
the three pairings structurally, rather than depending on an arbitrary enumeration order: the
adjacent, crossing, and nested pairings have weights `1`, `ζ`, and `1`, respectively.

This file is purely combinatorial.  It does not define operator-valued time ordering, contractions,
thermal expectations, or a Wick theorem, and it imports neither statistics-specific implementation
directory.
-/

namespace SecondQuantization
namespace Common

/-- A normalized pair of ordered positions used in a Wick pairing. -/
abbrev WickPair (n : ℕ) := Fin (2 * n) × Fin (2 * n)

/-- A finite set of normalized pairs is a Wick pairing when every position occurs in exactly one
pair.  Normalization (`a < b`) makes the ordered crossing relation canonical. -/
def IsWickPairing {n : ℕ} (pairs : Finset (WickPair n)) : Prop :=
  pairs.filter (fun pair => pair.1 < pair.2) = pairs ∧
    (Finset.univ : Finset (Fin (2 * n))).filter (fun i =>
      (pairs.filter fun pair => pair.1 = i ∨ pair.2 = i).card = 1) = Finset.univ

instance decidableIsWickPairing {n : ℕ} (pairs : Finset (WickPair n)) :
    Decidable (IsWickPairing pairs) :=
  inferInstanceAs (Decidable (
    pairs.filter (fun pair => pair.1 < pair.2) = pairs ∧
      (Finset.univ : Finset (Fin (2 * n))).filter (fun i =>
        (pairs.filter fun pair => pair.1 = i ∨ pair.2 = i).card = 1) = Finset.univ))

/-- A perfect pairing of the linearly ordered positions `Fin (2 * n)`. -/
abbrev WickPairing (n : ℕ) := {pairs : Finset (WickPair n) // IsWickPairing pairs}

instance (n : ℕ) : Fintype (WickPairing n) := Subtype.fintype IsWickPairing

instance (n : ℕ) : DecidableEq (WickPairing n) := inferInstance

/-- Every pair stored in a Wick pairing is normalized. -/
theorem WickPairing.normalized {n : ℕ} (pairing : WickPairing n)
    {pair : WickPair n} (hpair : pair ∈ pairing.1) : pair.1 < pair.2 := by
  have hmem : pair ∈ pairing.1.filter (fun stored => stored.1 < stored.2) := by
    rw [pairing.2.1]
    exact hpair
  exact (Finset.mem_filter.mp hmem).2

/-- Every ordered position occurs in exactly one stored pair. -/
theorem WickPairing.occurrence_card {n : ℕ} (pairing : WickPairing n)
    (i : Fin (2 * n)) :
    (pairing.1.filter fun pair => pair.1 = i ∨ pair.2 = i).card = 1 := by
  have hmem : i ∈ (Finset.univ : Finset (Fin (2 * n))).filter (fun position =>
      (pairing.1.filter fun pair => pair.1 = position ∨ pair.2 = position).card = 1) := by
    rw [pairing.2.2]
    simp
  exact (Finset.mem_filter.mp hmem).2

/-- The finite enumeration of all Wick pairings of `Fin (2 * n)`. -/
def allWickPairings (n : ℕ) : Finset (WickPairing n) := Finset.univ

@[simp]
theorem mem_allWickPairings (pairing : WickPairing n) : pairing ∈ allWickPairings n := by
  simp [allWickPairings]

/-- The normalized pair `(a, b)` crosses `(c, d)` when `a < c < b < d`. -/
def WickPair.Crosses {n : ℕ} (left right : WickPair n) : Prop :=
  left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2

instance WickPair.decidableCrosses {n : ℕ} (left right : WickPair n) :
    Decidable (WickPair.Crosses left right) :=
  inferInstanceAs (Decidable (
    left.1 < right.1 ∧ right.1 < left.2 ∧ left.2 < right.2))

/-- The number of geometric crossings of a Wick pairing.  Because pairs are normalized and
`Crosses` fixes the order of their left endpoints, each crossing is counted exactly once. -/
def WickPairing.crossingCount {n : ℕ} (pairing : WickPairing n) : ℕ :=
  ((pairing.1.product pairing.1).filter fun pairPair : WickPair n × WickPair n =>
    WickPair.Crosses pairPair.1 pairPair.2).card

/-- The exchange-statistics weight `ζ ^ crossings` of a Wick pairing. -/
noncomputable def WickPairing.weight (s : Statistics) {n : ℕ}
    (pairing : WickPairing n) : ℂ :=
  (s.zetaInt : ℂ) ^ pairing.crossingCount

@[simp]
theorem WickPairing.weight_boson {n : ℕ} (pairing : WickPairing n) :
    pairing.weight Statistics.boson = 1 := by
  simp [WickPairing.weight]

@[simp]
theorem WickPairing.weight_fermion {n : ℕ} (pairing : WickPairing n) :
    pairing.weight Statistics.fermion = (-1 : ℂ) ^ pairing.crossingCount := by
  simp [WickPairing.weight]

/-- For fermions, the Wick weight is the parity sign of the crossing count. -/
theorem WickPairing.weight_fermion_eq_ite {n : ℕ} (pairing : WickPairing n) :
    pairing.weight Statistics.fermion =
      if Even pairing.crossingCount then 1 else -1 := by
  rw [WickPairing.weight_fermion, neg_one_pow_eq_ite]

/-- The adjacent four-position pairing `(0,1)(2,3)`. -/
def wickPairingAdjacent : WickPairing 2 :=
  ⟨{(0, 1), (2, 3)}, by decide⟩

/-- The crossing four-position pairing `(0,2)(1,3)`. -/
def wickPairingCrossing : WickPairing 2 :=
  ⟨{(0, 2), (1, 3)}, by decide⟩

/-- The nested four-position pairing `(0,3)(1,2)`. -/
def wickPairingNested : WickPairing 2 :=
  ⟨{(0, 3), (1, 2)}, by decide⟩

/- There are exactly three pairings of four ordered positions, stated as a `Finset` equality so
the result is independent of any enumeration order. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem allWickPairings_two :
    allWickPairings 2 = {wickPairingAdjacent, wickPairingCrossing, wickPairingNested} := by
  decide

@[simp]
theorem crossingCount_wickPairingAdjacent : wickPairingAdjacent.crossingCount = 0 := by
  decide

@[simp]
theorem crossingCount_wickPairingCrossing : wickPairingCrossing.crossingCount = 1 := by
  decide

@[simp]
theorem crossingCount_wickPairingNested : wickPairingNested.crossingCount = 0 := by
  decide

/-- Four-position sanity check: the three structural pairings have weights `1`, `ζ`, and `1`.
This is the combinatorial sign pattern behind the four-point Wick formula. -/
theorem four_position_pairings_and_weights (s : Statistics) :
    allWickPairings 2 = {wickPairingAdjacent, wickPairingCrossing, wickPairingNested} ∧
      wickPairingAdjacent.weight s = 1 ∧
      wickPairingCrossing.weight s = (s.zetaInt : ℂ) ∧
      wickPairingNested.weight s = 1 := by
  simp [allWickPairings_two, WickPairing.weight]

end Common
end SecondQuantization
