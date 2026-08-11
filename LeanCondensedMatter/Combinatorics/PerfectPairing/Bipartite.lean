import LeanCondensedMatter.Combinatorics.PerfectPairing.Core
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# Bipartite perfect-pairing matching

This module exposes only the semantic matching interface needed by downstream diagrammatics.

A `SideSplitting m` identifies the ambient positions `Fin (2 * m)` with two labelled sides of size
`m`. A perfect pairing is bipartite when every left position is paired with a right position. From
such a pairing, `Pairing.sideMatching` extracts the unique permutation matching the two sides.

Construction of pairings from permutations, normalized-pair enumeration, crossing/sign bookkeeping,
and pairing-sum reduction are implementation details of the exchange-sum backend and deliberately do
not belong to this public API.
-/

namespace Combinatorics

variable {m : ℕ}

/-- A *side splitting* of the ambient positions is an identification of `Fin (2 * m)` with two
labelled sides of size `m`. -/
abbrev SideSplitting (m : ℕ) := Fin m ⊕ Fin m ≃ Fin (2 * m)

/-- A pairing is *bipartite* for a side splitting when every left position is matched to a right
position. -/
def Pairing.IsBipartite (e : SideSplitting m) (P : Pairing m) : Prop :=
  ∀ i : Fin m, ∃ j : Fin m, P.partner (e (Sum.inl i)) = e (Sum.inr j)

private noncomputable def matchingTo (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) (i : Fin m) : Fin m :=
  Classical.choose (h i)

private theorem matchingTo_spec (e : SideSplitting m) {P : Pairing m} (h : P.IsBipartite e)
    (i : Fin m) : P.partner (e (Sum.inl i)) = e (Sum.inr (matchingTo e h i)) :=
  Classical.choose_spec (h i)

private theorem matchingTo_injective (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) : Function.Injective (matchingTo e h) := by
  intro i j hij
  have hspec := matchingTo_spec e h i
  rw [hij, ← matchingTo_spec e h j] at hspec
  exact Sum.inl.inj (e.injective (P.partner.injective hspec))

/-- The permutation matching the two sides of a bipartite pairing. -/
noncomputable def Pairing.sideMatching (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (matchingTo e h) (matchingTo_injective e h).bijective_of_finite

/-- Applying the extracted side matching gives exactly the right-side position paired to a left-side
position. -/
@[simp]
theorem Pairing.partner_sideMatching (e : SideSplitting m) {P : Pairing m}
    (h : P.IsBipartite e) (i : Fin m) :
    P.partner (e (Sum.inl i)) = e (Sum.inr (P.sideMatching e h i)) :=
  matchingTo_spec e h i

end Combinatorics
