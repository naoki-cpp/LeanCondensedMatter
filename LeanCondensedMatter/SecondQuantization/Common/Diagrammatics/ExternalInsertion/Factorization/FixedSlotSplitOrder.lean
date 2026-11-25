import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct

set_option linter.style.header false

/-!
# Fixed-order structure of the external/vacuum leg split

The external-support and complementary vacuum legs embed into the fixed ambient leg order.
The embeddings preserve the natural order in each sector. For four-legged interaction
vertices, the inter-sector fixed-order inversion count is even.

These lemmas describe the coordinate splitting itself, independently of vertex labels,
Wick pairings, mixed times, and particle statistics. Mixed-time permutation sign
factorization belongs to `Factorization.SlotSplitMixedSign`.
-/

namespace SecondQuantization
namespace Common

open Combinatorics
/-- The external-support side of the canonical fixed slot splitting preserves the
flattened order: external legs stay first, and the increasing support vertices retain
the order of their four local legs. -/
theorem externalInsertionSlotLegSplitting_left_strictMono
    {E N : ℕ} (T : Finset (Fin N)) :
    StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl p)) := by
  refine externalInsertionLegMap_strictMono
    (E := E) (E' := E) (T := T) (S := (Finset.univ : Finset (Fin N)))
    (Finset.subset_univ T) _ id (fun _ _ h => h) ?_ ?_
  · intro e
    exact externalInsertionSlotLegSplitting_external (E := E) (Finset.subset_univ T) e
  · intro v l
    exact externalInsertionSlotLegSplitting_left_interaction (E := E)
      (Finset.subset_univ T) v l

/-- A sorted vacuum leg, inserted into the full fixed-order array, occupies
the interaction-leg position of its original vertex. -/
private theorem externalInsertionSlotLegSplitting_fixedRight_apply
    {E N : ℕ} (T : Finset (Fin N))
    (v : Fin ((Finset.univ : Finset (Fin N)) \ T).card) (l : Fin 4) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order
          ((orderedQuarticLegEquiv S.card).symm (v, l)))) =
      externalInsertionInteractionLeg (E := E)
        (⟨(order v).1, Finset.mem_univ _⟩ :
          ↥(Finset.univ : Finset (Fin N))) l := by
  intro S order
  have hleg :
      orderedLegToDiagramLeg S order
          ((orderedQuarticLegEquiv S.card).symm (v, l)) =
        (quarticLegEquiv S).symm (order v, l) := by
    simp [orderedLegToDiagramLeg, Prod.map]
  rw [hleg]
  exact externalInsertionSlotLegSplitting_right_interaction
    (E := E) (Finset.subset_univ T) (order v) l

/-- The canonically ordered vacuum-sector legs retain their flat order when inserted
into the ambient fixed-order external-insertion leg array. -/
theorem externalInsertionSlotLegSplitting_orderedRight_strictMono
    {E N : ℕ} (T : Finset (Fin N)) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    StrictMono (fun p : Fin (2 * (2 * S.card)) =>
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order p))) := by
  intro S order
  refine externalInsertionLegMap_strictMono
    (E := 0) (E' := E) (T := S) (S := (Finset.univ : Finset (Fin N)))
    (Finset.subset_univ S) _ (fun e => Fin.elim0 e) ?_ ?_ ?_
  · intro e
    exact Fin.elim0 e
  · intro e
    exact Fin.elim0 e
  · intro v l
    let i := (S.orderIsoOfFin rfl).symm v
    let h : 2 * (2 * S.card) = S.card * 4 := by omega
    let p := (orderedQuarticLegEquiv S.card).symm (i, l)
    have hcoord : FiniteIndex.blockEquiv h p = (i, l) := by
      change orderedQuarticLegEquiv S.card p = (i, l)
      exact Equiv.apply_symm_apply _ _
    have hp : p = externalInsertionInteractionLeg (E := 0) v l := by
      have hv := congrArg Fin.val (FiniteIndex.eq_cast_mul_add_blockEquiv h p)
      rw [hcoord] at hv
      apply Fin.ext
      rw [externalInsertionInteractionLeg_val]
      simpa only [Fin.val_cast, Fin.val_mk, Prod.fst, Prod.snd,
        Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_comm, Nat.add_comm, i] using hv
    change externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
      (Sum.inr (orderedLegToDiagramLeg S order
        (externalInsertionInteractionLeg (E := 0) v l))) = _
    rw [← hp]
    have hright := externalInsertionSlotLegSplitting_fixedRight_apply (E := E) T i l
    change externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
      (Sum.inr (orderedLegToDiagramLeg S order p)) =
        externalInsertionInteractionLeg (E := E)
          (⟨(order i).1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) l at hright
    have hi : order i = v := (S.orderIsoOfFin rfl).apply_symm_apply v
    rw [hi] at hright
    exact hright

/-- A vacuum interaction leg precedes a support interaction leg precisely when
its ambient vertex precedes the support vertex; local quartic indices do not matter. -/
private theorem externalInsertionSlotLegSplitting_fixedRight_lt_leftInteraction_iff
    {E N : ℕ} (T : Finset (Fin N))
    (v : ↥T) (l : Fin 4)
    (w : Fin ((Finset.univ : Finset (Fin N)) \ T).card) (k : Fin 4) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order
          ((orderedQuarticLegEquiv S.card).symm (w, k)))) <
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionInteractionLeg (E := E) v l)) ↔
      (order w).1 < v.1 := by
  intro S order
  rw [externalInsertionSlotLegSplitting_fixedRight_apply]
  unfold externalInsertionInteractionLeg
  rw [externalInsertionSlotLegSplitting_left_interaction]
  change externalInsertionInteractionLeg (E := E)
      (⟨(order w).1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) k <
    externalInsertionInteractionLeg (E := E)
      (⟨v.1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) l ↔
    (order w).1 < v.1
  rw [externalInsertionInteractionLeg_lt_iff]
  have hne : (order w).1 ≠ v.1 := by
    intro h
    have hw : (order w).1 ∉ T := (Finset.mem_sdiff.mp (order w).2).2
    exact hw (h.symm ▸ v.2)
  have hne' :
      (⟨(order w).1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) ≠
        ⟨v.1, Finset.mem_univ _⟩ := fun h => hne (congrArg Subtype.val h)
  simp only [hne', false_and, or_false]
  rfl

/-- A vacuum interaction leg never precedes an external leg in fixed flattened order. -/
private theorem externalInsertionSlotLegSplitting_fixedRight_not_lt_leftExternal
    {E N : ℕ} (T : Finset (Fin N))
    (e : Fin (2 * E))
    (w : Fin ((Finset.univ : Finset (Fin N)) \ T).card) (k : Fin 4) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    ¬ externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order
          ((orderedQuarticLegEquiv S.card).symm (w, k)))) <
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionExternalLeg E T e)) := by
  intro S order
  rw [externalInsertionSlotLegSplitting_fixedRight_apply]
  unfold externalInsertionExternalLeg
  rw [externalInsertionSlotLegSplitting_external]
  change ¬ (externalInsertionInteractionLeg (E := E)
      (⟨(order w).1, Finset.mem_univ _⟩ :
        ↥(Finset.univ : Finset (Fin N))) k).val <
      (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) e).val
  simp only [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
  have he := e.isLt
  omega

/-- The canonical support/vacuum split has an even fixed-order inter-sector
inversion count: each vacuum vertex contributes four indistinguishable comparisons
against any given support leg, and vacuum legs never precede external legs. -/
theorem externalInsertionSlotLegSplitting_fixedInversionCount_mod_two_eq_zero
    {E N : ℕ} (T : Finset (Fin N)) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    (∑ i : Fin (2 * (2 * T.card + E)),
      ∑ j : Fin (2 * (2 * S.card)),
        if externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inr (orderedLegToDiagramLeg S order j)) <
            externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inl i)
          then 1 else 0) % 2 = 0 := by
  classical
  intro S order
  apply Nat.mod_eq_zero_of_dvd
  refine Finset.dvd_sum fun i _ => ?_
  let leg := externalInsertionLegEquiv E T i
  have hi : (externalInsertionLegEquiv E T).symm leg = i := by simp [leg]
  rw [← hi]
  cases leg with
  | inl e =>
      apply Finset.dvd_sum
      intro j _
      let vl := orderedQuarticLegEquiv S.card j
      have hj : (orderedQuarticLegEquiv S.card).symm vl = j := by simp [vl]
      rw [← hj]
      have hzero :
          (if externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inr (orderedLegToDiagramLeg S order
                  ((orderedQuarticLegEquiv S.card).symm vl))) <
              externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inl e)))
            then (1 : ℕ) else 0) = 0 :=
        ite_eq_right
          (externalInsertionSlotLegSplitting_fixedRight_not_lt_leftExternal
            (E := E) T e vl.1 vl.2)
      rw [hzero]
      exact dvd_zero 2
  | inr vl =>
      rcases vl with ⟨v, l⟩
      have hdiv := Fintype.dvd_sum_equiv_fst_of_dvd_card
        (orderedQuarticLegEquiv S.card)
        (fun w : Fin S.card => if (order w).1 < v.1 then (1 : ℕ) else 0)
        (by decide : 2 ∣ Fintype.card (Fin 4))
      convert hdiv using 1
      apply Finset.sum_congr rfl
      intro j _
      let wk := orderedQuarticLegEquiv S.card j
      have hj : (orderedQuarticLegEquiv S.card).symm wk = j := by simp [wk]
      rw [← hj]
      have hiff :=
        externalInsertionSlotLegSplitting_fixedRight_lt_leftInteraction_iff
          (E := E) T v l wk.1 wk.2
      dsimp only at hiff
      simp only [Equiv.apply_symm_apply]
      have hiff' :
          externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inr (orderedLegToDiagramLeg S order
                ((orderedQuarticLegEquiv S.card).symm wk))) <
            externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inr (v, l)))) ↔
            (order wk.1).1 < v.1 := by
        change
          externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inr (orderedLegToDiagramLeg S order
                ((orderedQuarticLegEquiv S.card).symm wk))) <
            externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inr (v, l)))) ↔
            (order wk.1).1 < v.1 at hiff
        exact hiff
      simp only [hiff']


end Common
end SecondQuantization
