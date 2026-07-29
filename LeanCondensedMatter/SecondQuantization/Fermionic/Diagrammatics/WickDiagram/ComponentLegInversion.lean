import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.ComponentPairing

set_option linter.style.header false

/-!
# Cross-component quartic-leg inversions

For distinct components, the relative order of two assembled flattened legs is determined entirely
by the relative order of their vertex slots: the four local legs occupy one contiguous block.  It
follows that a reversed pair of vertex slots contributes exactly `4 × 4 = 16` reversed leg pairs.
-/

namespace SecondQuantization

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
          ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ <
        shuffle.slotEquiv
          ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ := by
  have hpLocal :
      (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2.val < 4 :=
    (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2.isLt
  have hqLocal :
      (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).2.val < 4 :=
    (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).2.isLt
  have hslot_ne :
      (shuffle.slotEquiv
        ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩).val ≠
      (shuffle.slotEquiv
        ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩).val := by
    intro hval
    have hslot :
        shuffle.slotEquiv
            ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩ =
          shuffle.slotEquiv
            ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩ :=
      Fin.ext hval
    have hsigma := shuffle.slotEquiv.injective hslot
    exact hBC (congrArg Sigma.fst hsigma)
  change (d.componentOrderedLeg shuffle B p).val <
      (d.componentOrderedLeg shuffle C q).val ↔
    (shuffle.slotEquiv
      ⟨B, (orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩).val <
    (shuffle.slotEquiv
      ⟨C, (orderedQuarticLegEquiv (C : Finset (Fin N)).card q).1⟩).val
  rw [d.componentOrderedLeg_val, d.componentOrderedLeg_val]
  omega

/-- A reversed pair of distinct-component vertex slots contributes all `4 × 4 = 16` reversed
quartic-leg pairs, while a correctly ordered pair contributes none. -/
theorem QuarticWickDiagram.sum_componentOrderedLeg_inversions_at_vertices
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B C : d.componentPartition.parts) (hBC : B ≠ C)
    (i : Fin (B : Finset (Fin N)).card) (j : Fin (C : Finset (Fin N)).card) :
    (∑ localB : Fin 4, ∑ localC : Fin 4,
      if d.componentOrderedLeg shuffle C
          ((orderedQuarticLegEquiv (C : Finset (Fin N)).card).symm (j, localC)) <
        d.componentOrderedLeg shuffle B
          ((orderedQuarticLegEquiv (B : Finset (Fin N)).card).symm (i, localB))
      then 1 else 0) =
      if shuffle.slotEquiv ⟨C, j⟩ < shuffle.slotEquiv ⟨B, i⟩ then 16 else 0 := by
  classical
  simp_rw [d.componentOrderedLeg_lt_componentOrderedLeg_iff_slot_lt
    shuffle C B (Ne.symm hBC)]
  simp

end SecondQuantization
