import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

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
        rw [← hy, P.partner_partner]
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

end Combinatorics
