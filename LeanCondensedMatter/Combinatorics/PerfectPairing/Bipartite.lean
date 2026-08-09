import LeanCondensedMatter.Combinatorics.PerfectPairing.Crossing
import Mathlib.Logic.Equiv.Fin.Basic

set_option linter.style.header false

/-!
# Bipartite perfect pairings

Splitting the ambient positions `Fin (2 * m)` into a first and a second half of size `m`, every
permutation of `Fin m` determines a perfect pairing that matches each position of the first half
with a position of the second half, and every pairing with that property arises this way.

This is the representation in which a fermionic pairing sum becomes a determinant: the pairs are
indexed by a permutation rather than by a general matching, and each pair is automatically
normalized because the whole first half precedes the whole second half.
-/

namespace Combinatorics

variable {m : ℕ}

/-- Ambient positions of a pairing of `Fin (2 * m)`, split into a first and a second half. -/
def bipartiteHalfEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

@[simp]
theorem bipartiteHalfEquiv_inl_val (m : ℕ) (i : Fin m) :
    (bipartiteHalfEquiv m (Sum.inl i)).val = i.val := by
  simp [bipartiteHalfEquiv]

@[simp]
theorem bipartiteHalfEquiv_inr_val (m : ℕ) (i : Fin m) :
    (bipartiteHalfEquiv m (Sum.inr i)).val = m + i.val := by
  simp [bipartiteHalfEquiv]
  omega

/-- Every position of the first half precedes every position of the second half. -/
theorem bipartiteHalfEquiv_inl_lt_inr (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inl i) < bipartiteHalfEquiv m (Sum.inr j) := by
  have hi := i.isLt
  change (bipartiteHalfEquiv m (Sum.inl i)).val < (bipartiteHalfEquiv m (Sum.inr j)).val
  rw [bipartiteHalfEquiv_inl_val, bipartiteHalfEquiv_inr_val]
  omega

/-- Positions inside the first half compare as their indices do. -/
theorem bipartiteHalfEquiv_inl_lt_inl_iff (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inl i) < bipartiteHalfEquiv m (Sum.inl j) ↔ i < j := by
  change (bipartiteHalfEquiv m (Sum.inl i)).val < (bipartiteHalfEquiv m (Sum.inl j)).val ↔ _
  rw [bipartiteHalfEquiv_inl_val, bipartiteHalfEquiv_inl_val]
  exact Iff.rfl

/-- Positions inside the second half compare as their indices do. -/
theorem bipartiteHalfEquiv_inr_lt_inr_iff (m : ℕ) (i j : Fin m) :
    bipartiteHalfEquiv m (Sum.inr i) < bipartiteHalfEquiv m (Sum.inr j) ↔ i < j := by
  change (bipartiteHalfEquiv m (Sum.inr i)).val < (bipartiteHalfEquiv m (Sum.inr j)).val ↔ _
  rw [bipartiteHalfEquiv_inr_val, bipartiteHalfEquiv_inr_val]
  change _ ↔ i.val < j.val
  omega

/-- The involution sending each position of the first half to the position of the second half
selected by `σ`. -/
def bipartitePartner (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 * m)) :=
  ((bipartiteHalfEquiv m).symm.trans
      ((Equiv.sumComm (Fin m) (Fin m)).trans (Equiv.sumCongr σ.symm σ))).trans
    (bipartiteHalfEquiv m)

@[simp]
theorem bipartitePartner_inl (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    bipartitePartner σ (bipartiteHalfEquiv m (Sum.inl i)) =
      bipartiteHalfEquiv m (Sum.inr (σ i)) := by
  simp [bipartitePartner]

@[simp]
theorem bipartitePartner_inr (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    bipartitePartner σ (bipartiteHalfEquiv m (Sum.inr j)) =
      bipartiteHalfEquiv m (Sum.inl (σ.symm j)) := by
  simp [bipartitePartner]

theorem isPairing_bipartitePartner (σ : Equiv.Perm (Fin m)) :
    IsPairing (bipartitePartner σ) := by
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := (bipartiteHalfEquiv m).surjective x
    cases y with
    | inl i => simp
    | inr j => simp
  · intro x
    obtain ⟨y, rfl⟩ := (bipartiteHalfEquiv m).surjective x
    cases y with
    | inl i =>
        intro h
        rw [bipartitePartner_inl] at h
        have h' := (bipartiteHalfEquiv m).injective h
        simp at h'
    | inr j =>
        intro h
        rw [bipartitePartner_inr] at h
        have h' := (bipartiteHalfEquiv m).injective h
        simp at h'

/-- The perfect pairing of `Fin (2 * m)` matching the first half to the second half through `σ`. -/
def bipartitePairing (σ : Equiv.Perm (Fin m)) : Pairing m :=
  Pairing.ofPartner (bipartitePartner σ) (isPairing_bipartitePartner σ)

@[simp]
theorem bipartitePairing_partner (σ : Equiv.Perm (Fin m)) :
    (bipartitePairing σ).partner = bipartitePartner σ :=
  rfl

/-- The normalized pairs of a bipartite pairing are exactly the graph of `σ`, read across the two
halves. -/
theorem mem_bipartitePairing_pairs_iff (σ : Equiv.Perm (Fin m))
    (x y : Fin m ⊕ Fin m) :
    (bipartiteHalfEquiv m x, bipartiteHalfEquiv m y) ∈ (bipartitePairing σ).pairs ↔
      ∃ i : Fin m, x = Sum.inl i ∧ y = Sum.inr (σ i) := by
  rw [Pairing.mem_pairs_iff]
  constructor
  · rintro ⟨hlt, hpartner⟩
    cases x with
    | inl i =>
        refine ⟨i, rfl, ?_⟩
        rw [bipartitePairing_partner, bipartitePartner_inl] at hpartner
        exact ((bipartiteHalfEquiv m).injective hpartner).symm
    | inr j =>
        rw [bipartitePairing_partner, bipartitePartner_inr] at hpartner
        have hy := (bipartiteHalfEquiv m).injective hpartner
        subst hy
        exact absurd hlt (asymm (bipartiteHalfEquiv_inl_lt_inr m (σ.symm j) j))
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨bipartiteHalfEquiv_inl_lt_inr m i (σ i), by simp⟩

end Combinatorics
