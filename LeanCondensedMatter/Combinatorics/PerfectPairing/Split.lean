import LeanCondensedMatter.Combinatorics.PerfectPairing.Sign

set_option linter.style.header false

/-!
# Splitting a pairing along a decomposition of its positions

A *position splitting* presents the ambient positions of a pairing of `Fin (2 * n)` as two labelled
parts carrying `a` and `b` pairs. A pairing is *split* by it when no pair crosses between the parts;
such a pairing restricts to a pairing of each part.

This is the decomposition a connected-component factorization uses: the pairs of a Wick diagram
never join two different connected components, so the diagram's pairing restricts to each component.

Only the left part needs to be assumed closed under `partner`. Closure of the right part is
automatic, because `partner` is an involution: a right position paired to a left one would make that
left position paired to a right one.

Restricting and assembling are mutually inverse, so the pairings split by a given splitting are
exactly the pairs of pairings of the parts (`Pairing.splitEquiv`).

Compare `Combinatorics.SideSplitting`, where the pairs all *do* cross between the two parts. The two
are the extreme cases of the same presentation of the positions.
-/

namespace Combinatorics

variable {a b n : ℕ}

/-- A presentation of the ambient positions of a pairing of `Fin (2 * n)` as two parts carrying `a`
and `b` pairs. -/
abbrev PositionSplitting (a b n : ℕ) := Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * n)

/-- A pairing is *split* by a position splitting when the left part is closed under `partner`, so
that no pair joins the two parts. -/
def Pairing.IsSplit (e : PositionSplitting a b n) (P : Pairing n) : Prop :=
  ∀ i : Fin (2 * a), ∃ j : Fin (2 * a), P.partner (e (Sum.inl i)) = e (Sum.inl j)

theorem positionSplitting_inl_ne_inr (e : PositionSplitting a b n) (i : Fin (2 * a))
    (j : Fin (2 * b)) : e (Sum.inl i) ≠ e (Sum.inr j) := fun h => by simpa using e.injective h

/-- **The right part is closed automatically.** A right position paired to a left one would make
that left position paired to a right one, contradicting the left closure. -/
theorem Pairing.isSplit_inr (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)
    (i : Fin (2 * b)) : ∃ j : Fin (2 * b), P.partner (e (Sum.inr i)) = e (Sum.inr j) := by
  obtain ⟨y, hy⟩ := e.surjective (P.partner (e (Sum.inr i)))
  cases y with
  | inr j => exact ⟨j, hy.symm⟩
  | inl k =>
      obtain ⟨j, hj⟩ := h k
      have hback : P.partner (e (Sum.inl k)) = e (Sum.inr i) := by
        rw [hy, P.partner_partner]
      exact absurd (hback.symm.trans hj) (Ne.symm (positionSplitting_inl_ne_inr e j i))

section Left

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The partner of a left position, read back in the left part. -/
private noncomputable def splitLeftMap (i : Fin (2 * a)) : Fin (2 * a) :=
  Classical.choose (h i)

private theorem splitLeftMap_spec (i : Fin (2 * a)) :
    P.partner (e (Sum.inl i)) = e (Sum.inl (splitLeftMap e h i)) :=
  Classical.choose_spec (h i)

private theorem splitLeftMap_involutive : Function.Involutive (splitLeftMap e h) := by
  intro i
  have h1 := splitLeftMap_spec e h i
  have h2 := splitLeftMap_spec e h (splitLeftMap e h i)
  have : e (Sum.inl i) = e (Sum.inl (splitLeftMap e h (splitLeftMap e h i))) := by
    rw [← h2, ← h1, P.partner_partner]
  exact (Sum.inl.inj (e.injective this)).symm

private theorem splitLeftMap_ne_self (i : Fin (2 * a)) : splitLeftMap e h i ≠ i := by
  intro hi
  have := splitLeftMap_spec e h i
  rw [hi] at this
  exact absurd this (P.partner_ne _)

/-- The pairing induced on the left part. -/
noncomputable def Pairing.splitLeft : Pairing a :=
  Pairing.ofPartner (Function.Involutive.toPerm _ (splitLeftMap_involutive e h))
    ⟨splitLeftMap_involutive e h, splitLeftMap_ne_self e h⟩

/-- The induced left pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitLeft (i : Fin (2 * a)) :
    P.partner (e (Sum.inl i)) = e (Sum.inl ((P.splitLeft e h).partner i)) :=
  splitLeftMap_spec e h i

end Left

section Right

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The partner of a right position, read back in the right part. -/
private noncomputable def splitRightMap (i : Fin (2 * b)) : Fin (2 * b) :=
  Classical.choose (P.isSplit_inr e h i)

private theorem splitRightMap_spec (i : Fin (2 * b)) :
    P.partner (e (Sum.inr i)) = e (Sum.inr (splitRightMap e h i)) :=
  Classical.choose_spec (P.isSplit_inr e h i)

private theorem splitRightMap_involutive : Function.Involutive (splitRightMap e h) := by
  intro i
  have h1 := splitRightMap_spec e h i
  have h2 := splitRightMap_spec e h (splitRightMap e h i)
  have : e (Sum.inr i) = e (Sum.inr (splitRightMap e h (splitRightMap e h i))) := by
    rw [← h2, ← h1, P.partner_partner]
  exact (Sum.inr.inj (e.injective this)).symm

private theorem splitRightMap_ne_self (i : Fin (2 * b)) : splitRightMap e h i ≠ i := by
  intro hi
  have := splitRightMap_spec e h i
  rw [hi] at this
  exact absurd this (P.partner_ne _)

/-- The pairing induced on the right part. -/
noncomputable def Pairing.splitRight : Pairing b :=
  Pairing.ofPartner (Function.Involutive.toPerm _ (splitRightMap_involutive e h))
    ⟨splitRightMap_involutive e h, splitRightMap_ne_self e h⟩

/-- The induced right pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitRight (i : Fin (2 * b)) :
    P.partner (e (Sum.inr i)) = e (Sum.inr ((P.splitRight e h).partner i)) :=
  splitRightMap_spec e h i

end Right

section Assemble

private theorem sumCongr_involutive {α β : Type*} (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : Function.Involutive p) (hq : Function.Involutive q) :
    Function.Involutive (Equiv.sumCongr p q) := by
  rintro (x | x)
  · exact congrArg Sum.inl (hp x)
  · exact congrArg Sum.inr (hq x)

private theorem sumCongr_ne_self {α β : Type*} (p : Equiv.Perm α) (q : Equiv.Perm β)
    (hp : ∀ x, p x ≠ x) (hq : ∀ x, q x ≠ x) (x : α ⊕ β) :
    Equiv.sumCongr p q x ≠ x := by
  rcases x with x | x
  · exact fun h => hp x (Sum.inl.inj h)
  · exact fun h => hq x (Sum.inr.inj h)

/-- **Assemble a pairing from a pairing on each part.** Inverse construction to `splitLeft` and
`splitRight`: no pair joins the two parts, so the two partner maps can simply be run side by side. -/
noncomputable def Pairing.ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    Pairing n :=
  Pairing.ofPartner (e.permCongr (Equiv.sumCongr P.partner Q.partner))
    (IsPairing.permCongr
      ⟨sumCongr_involutive _ _ P.partner_involutive Q.partner_involutive,
        sumCongr_ne_self _ _ P.partner_ne Q.partner_ne⟩ e)

@[simp]
theorem Pairing.ofSplit_partner_inl (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * a)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inl i)) = e (Sum.inl (P.partner i)) := by
  change e (Equiv.sumCongr P.partner Q.partner (e.symm (e (Sum.inl i)))) = _
  rw [e.symm_apply_apply]
  rfl

@[simp]
theorem Pairing.ofSplit_partner_inr (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * b)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inr i)) = e (Sum.inr (Q.partner i)) := by
  change e (Equiv.sumCongr P.partner Q.partner (e.symm (e (Sum.inr i)))) = _
  rw [e.symm_apply_apply]
  rfl

/-- An assembled pairing is split by the splitting it was assembled along. -/
theorem Pairing.isSplit_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).IsSplit e := fun i =>
  ⟨P.partner i, Pairing.ofSplit_partner_inl e P Q i⟩

end Assemble

section Inverse

/-- Assembling and then restricting to the left part returns the left pairing. -/
@[simp]
theorem Pairing.splitLeft_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitLeft e (Pairing.isSplit_ofSplit e P Q) = P := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitLeft e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inl] at h
  exact (Sum.inl.inj (e.injective h)).symm

/-- Assembling and then restricting to the right part returns the right pairing. -/
@[simp]
theorem Pairing.splitRight_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitRight e (Pairing.isSplit_ofSplit e P Q) = Q := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitRight e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inr] at h
  exact (Sum.inr.inj (e.injective h)).symm

/-- **A split pairing is assembled from its two restrictions.** Nothing is lost by taking a split
pairing apart: every position lies in one of the parts, and its partner lies in the same part. -/
@[simp]
theorem Pairing.ofSplit_splitLeft_splitRight (e : PositionSplitting a b n) {P : Pairing n}
    (h : P.IsSplit e) :
    Pairing.ofSplit e (P.splitLeft e h) (P.splitRight e h) = P := by
  refine Pairing.ext (Equiv.ext fun i => ?_)
  obtain ⟨x, rfl⟩ := e.surjective i
  cases x with
  | inl j => rw [Pairing.ofSplit_partner_inl, Pairing.partner_splitLeft e h]
  | inr j => rw [Pairing.ofSplit_partner_inr, Pairing.partner_splitRight e h]

/-- **The pairings split by a position splitting are exactly the pairs of part pairings.**

This is the combinatorial content of a binary diagram decomposition: choosing a pairing that
respects the splitting is the same as choosing one on each part independently. A reindexing of a sum
over diagrams as a sum over pairs of pieces goes through this equivalence. -/
noncomputable def Pairing.splitEquiv (e : PositionSplitting a b n) :
    {P : Pairing n // P.IsSplit e} ≃ Pairing a × Pairing b where
  toFun P := (P.1.splitLeft e P.2, P.1.splitRight e P.2)
  invFun PQ := ⟨Pairing.ofSplit e PQ.1 PQ.2, Pairing.isSplit_ofSplit e PQ.1 PQ.2⟩
  left_inv P := Subtype.ext (Pairing.ofSplit_splitLeft_splitRight e P.2)
  right_inv PQ := by
    obtain ⟨P, Q⟩ := PQ
    simp only [Prod.mk.injEq]
    exact ⟨Pairing.splitLeft_ofSplit e P Q, Pairing.splitRight_ofSplit e P Q⟩

end Inverse

end Combinatorics
