import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairing

set_option linter.style.header false

/-!
# Cross-component quartic-leg inversions

For distinct components, the relative order of two assembled flattened legs is determined entirely
by the relative order of their vertex slots: the four local legs occupy one contiguous block. It
follows that a reversed pair of vertex slots contributes exactly `4 × 4 = 16` reversed leg pairs.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

/-- For distinct components, comparison of assembled legs is exactly comparison of their global
vertex slots. -/
theorem QuarticWickDiagram.componentOrderedLeg_lt_componentOrderedLeg_iff_slot_lt
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card)))
    (q : Fin (2 * (2 * (C : Finset (Fin N)).card))) :
    d.componentOrderedLeg shuffle B p < d.componentOrderedLeg shuffle C q ↔
      shuffle.slotEquiv
          ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ <
        shuffle.slotEquiv
          ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
  have hslot_ne :
      shuffle.slotEquiv
          ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ ≠
        shuffle.slotEquiv
          ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
    intro hslot
    have hsigma := shuffle.slotEquiv.injective hslot
    exact hBC (congrArg Sigma.fst hsigma)
  unfold QuarticWickDiagram.componentOrderedLeg
  exact orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne S.card
    (shuffle.slotEquiv
      ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩)
    (shuffle.slotEquiv
      ⟨C, (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩)
    (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2
    (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card q).2 hslot_ne

/-- A reversed pair of distinct-component vertex slots contributes all `4 × 4 = 16` reversed
quartic-leg pairs, while a correctly ordered pair contributes none. -/
theorem QuarticWickDiagram.sum_componentOrderedLeg_inversions_at_vertices
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (i : Fin (B : Finset (Fin N)).card) (j : Fin (C : Finset (Fin N)).card) :
    (∑ localB : Fin 4, ∑ localC : Fin 4,
      if d.componentOrderedLeg shuffle C
          ((Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card).symm (j, localC)) <
        d.componentOrderedLeg shuffle B
          ((Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm (i, localB))
      then 1 else 0) =
      if shuffle.slotEquiv ⟨C, j⟩ < shuffle.slotEquiv ⟨B, i⟩ then 16 else 0 := by
  classical
  simp_rw [d.componentOrderedLeg_lt_componentOrderedLeg_iff_slot_lt
    shuffle C B (Ne.symm hBC)]
  simp

/-- Summing over all legs of two distinct components is the same as summing a `0`-or-`16`
contribution over their vertex pairs. -/
theorem QuarticWickDiagram.sum_componentOrderedLeg_inversions_eq_sum_vertex_inversions
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C) :
    (∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
      ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
        if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
        then 1 else 0) =
      ∑ i : Fin (B : Finset (Fin N)).card,
        ∑ j : Fin (C : Finset (Fin N)).card,
          if shuffle.slotEquiv ⟨C, j⟩ < shuffle.slotEquiv ⟨B, i⟩ then 16 else 0 := by
  classical
  let legPairEquiv :
      (Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
        Fin (2 * (2 * (C : Finset (Fin N)).card))) ≃
        ((Fin (B : Finset (Fin N)).card × Fin (C : Finset (Fin N)).card) ×
          (Fin 4 × Fin 4)) :=
    (Equiv.prodCongr
      (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card)
      (Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card)).trans
      (Equiv.prodProdProdComm _ _ _ _)
  calc
    (∑ p : Fin (2 * (2 * (B : Finset (Fin N)).card)),
        ∑ q : Fin (2 * (2 * (C : Finset (Fin N)).card)),
          if d.componentOrderedLeg shuffle C q < d.componentOrderedLeg shuffle B p
          then 1 else 0) =
      ∑ x : Fin (2 * (2 * (B : Finset (Fin N)).card)) ×
          Fin (2 * (2 * (C : Finset (Fin N)).card)),
        if d.componentOrderedLeg shuffle C x.2 < d.componentOrderedLeg shuffle B x.1
        then 1 else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ x : (Fin (B : Finset (Fin N)).card × Fin (C : Finset (Fin N)).card) ×
          (Fin 4 × Fin 4),
        if d.componentOrderedLeg shuffle C
            ((Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card).symm (x.1.2, x.2.2)) <
          d.componentOrderedLeg shuffle B
            ((Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm (x.1.1, x.2.1))
        then 1 else 0 := by
          refine Fintype.sum_equiv legPairEquiv
            (fun x => if d.componentOrderedLeg shuffle C x.2 <
              d.componentOrderedLeg shuffle B x.1 then 1 else 0)
            (fun x => if d.componentOrderedLeg shuffle C
                ((Common.orderedQuarticLegEquiv (C : Finset (Fin N)).card).symm (x.1.2, x.2.2)) <
              d.componentOrderedLeg shuffle B
                ((Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm (x.1.1, x.2.1))
              then 1 else 0) ?_
          intro x
          simp [legPairEquiv]
    _ = ∑ i : Fin (B : Finset (Fin N)).card,
        ∑ j : Fin (C : Finset (Fin N)).card,
          if shuffle.slotEquiv ⟨C, j⟩ < shuffle.slotEquiv ⟨B, i⟩ then 16 else 0 := by
          simp only [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact d.sum_componentOrderedLeg_inversions_at_vertices shuffle B C hBC i j

end Fermionic
end SecondQuantization
