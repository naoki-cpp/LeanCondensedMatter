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


private def sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (2 * m)) :=
  ((e.symm.trans ((Equiv.sumComm (Fin m) (Fin m)).trans (Equiv.sumCongr σ.symm σ))).trans e)

private theorem sidePartner_inl (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    sidePartner e σ (e (Sum.inl i)) = e (Sum.inr (σ i)) := by
  simp [sidePartner]

private theorem sidePartner_inr (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    sidePartner e σ (e (Sum.inr j)) = e (Sum.inl (σ.symm j)) := by
  simp [sidePartner]

private theorem isPairing_sidePartner (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    IsPairing (sidePartner e σ) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl i => simp [sidePartner_inl, sidePartner_inr]
    | inr j => simp [sidePartner_inl, sidePartner_inr]
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl i =>
        intro h
        rw [sidePartner_inl] at h
        have h' := e.injective h
        simp at h'
    | inr j =>
        intro h
        rw [sidePartner_inr] at h
        have h' := e.injective h
        simp at h'

private def pairingOfSideMatching (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) : Pairing m :=
  PairingOn.ofPartner (sidePartner e σ) (isPairing_sidePartner e σ)

private theorem pairingOfSideMatching_partner_inl
    (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (pairingOfSideMatching e σ).partner (e (Sum.inl i)) = e (Sum.inr (σ i)) :=
  sidePartner_inl e σ i

private theorem pairingOfSideMatching_partner_inr
    (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    (pairingOfSideMatching e σ).partner (e (Sum.inr j)) = e (Sum.inl (σ.symm j)) :=
  sidePartner_inr e σ j

private theorem pairingOfSideMatching_isBipartite
    (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) :
    (pairingOfSideMatching e σ).IsBipartite e :=
  fun i => ⟨σ i, pairingOfSideMatching_partner_inl e σ i⟩

/-- Bipartite pairings for a fixed side splitting are canonically equivalent to permutations
matching the left side to the right side. -/
noncomputable def Pairing.bipartiteEquivPerm (e : SideSplitting m) :
    {P : Pairing m // P.IsBipartite e} ≃ Equiv.Perm (Fin m) where
  toFun P := P.1.sideMatching e P.2
  invFun σ := ⟨pairingOfSideMatching e σ, pairingOfSideMatching_isBipartite e σ⟩
  left_inv P := by
    apply Subtype.ext
    refine PairingOn.ext (Equiv.ext fun x => ?_)
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y with
    | inl i =>
        rw [pairingOfSideMatching_partner_inl, ← Pairing.partner_sideMatching e P.2 i]
    | inr j =>
        rw [pairingOfSideMatching_partner_inr]
        have hi := Pairing.partner_sideMatching e P.2 ((P.1.sideMatching e P.2).symm j)
        rw [Equiv.apply_symm_apply] at hi
        rw [← hi, P.1.partner_partner]
  right_inv σ := by
    apply Equiv.ext
    intro i
    have h := Pairing.partner_sideMatching e (pairingOfSideMatching_isBipartite e σ) i
    rw [pairingOfSideMatching_partner_inl] at h
    exact (Sum.inr.inj (e.injective h)).symm

@[simp]
theorem Pairing.bipartiteEquivPerm_symm_partner_inl
    (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (((Pairing.bipartiteEquivPerm e).symm σ).1).partner (e (Sum.inl i)) =
      e (Sum.inr (σ i)) := by
  exact pairingOfSideMatching_partner_inl e σ i

@[simp]
theorem Pairing.bipartiteEquivPerm_symm_partner_inr
    (e : SideSplitting m) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    (((Pairing.bipartiteEquivPerm e).symm σ).1).partner (e (Sum.inr j)) =
      e (Sum.inl (σ.symm j)) := by
  exact pairingOfSideMatching_partner_inr e σ j

end Combinatorics
