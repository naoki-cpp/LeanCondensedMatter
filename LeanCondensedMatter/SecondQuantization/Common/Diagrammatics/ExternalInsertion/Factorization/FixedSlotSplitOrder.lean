import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Combinatorics.FiniteIndex.Block
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
  let localEquiv := externalInsertionLegEquiv E T
  intro a b hab
  let la := localEquiv a
  let lb := localEquiv b
  have ha : localEquiv.symm la = a := by simp [la]
  have hb : localEquiv.symm lb = b := by simp [lb]
  rw [← ha, ← hb] at hab ⊢
  rcases la with e | ⟨v, l⟩ <;> rcases lb with f | ⟨w, k⟩
  · change (externalInsertionExternalLeg E T e).val <
        (externalInsertionExternalLeg E T f).val at hab
    change externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionExternalLeg E T e)) <
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionExternalLeg E T f))
    unfold externalInsertionExternalLeg
    rw [externalInsertionSlotLegSplitting_external,
      externalInsertionSlotLegSplitting_external]
    change (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) e).val <
      (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) f).val
    simpa only [Fin.lt_def, externalInsertionExternalLeg_val] using hab
  · change externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionExternalLeg E T e)) <
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionInteractionLeg (E := E) w k))
    unfold externalInsertionExternalLeg externalInsertionInteractionLeg
    rw [externalInsertionSlotLegSplitting_external,
      externalInsertionSlotLegSplitting_left_interaction]
    change (externalInsertionExternalLeg E (Finset.univ : Finset (Fin N)) e).val <
      (externalInsertionInteractionLeg (E := E)
        (⟨w.1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) k).val
    simp only [externalInsertionExternalLeg_val, externalInsertionInteractionLeg_val]
    have he := e.isLt
    omega
  · change (externalInsertionInteractionLeg (E := E) v l).val <
      (externalInsertionExternalLeg E T f).val at hab
    simp only [externalInsertionInteractionLeg_val,
      externalInsertionExternalLeg_val] at hab
    have hf := f.isLt
    omega
  · change (externalInsertionInteractionLeg (E := E) v l).val <
      (externalInsertionInteractionLeg (E := E) w k).val at hab
    change externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionInteractionLeg (E := E) v l)) <
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl (externalInsertionInteractionLeg (E := E) w k))
    unfold externalInsertionInteractionLeg
    rw [externalInsertionSlotLegSplitting_left_interaction,
      externalInsertionSlotLegSplitting_left_interaction]
    change (externalInsertionInteractionLeg (E := E)
        (⟨v.1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) l).val <
      (externalInsertionInteractionLeg (E := E)
        (⟨w.1, Finset.mem_univ _⟩ : ↥(Finset.univ : Finset (Fin N))) k).val
    simp only [externalInsertionInteractionLeg_val] at hab ⊢
    have huniv (x : Fin N) :
        (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm
          ⟨x, Finset.mem_univ x⟩).val = x.val := by
      rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
    rw [huniv, huniv]
    by_cases hvw : v = w
    · subst w
      omega
    · have hrank_ne :
          ((T.orderIsoOfFin rfl).symm v).val ≠
            ((T.orderIsoOfFin rfl).symm w).val := by
        intro h
        apply hvw
        exact (T.orderIsoOfFin rfl).symm.injective (Fin.ext h)
      have hrank :
          ((T.orderIsoOfFin rfl).symm v).val <
            ((T.orderIsoOfFin rfl).symm w).val := by
        have hl := l.isLt
        have hk := k.isLt
        omega
      have hvertex : v.1 < w.1 := by
        have h := (T.orderIsoOfFin rfl).strictMono (Fin.lt_def.mpr hrank)
        simpa using h
      have hl := l.isLt
      have hk := k.isLt
      omega

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
  let vertex : Fin S.card → Fin N := fun i => (S.orderIsoOfFin rfl i).1
  have hvertex : StrictMono vertex := by
    intro i j hij
    exact (S.orderIsoOfFin rfl).strictMono hij
  let hsource : 2 * (2 * S.card) = S.card * 4 := by omega
  let htarget : 2 * (2 * N) = N * 4 := by omega
  let block := FiniteIndex.blockMap hsource htarget vertex
  have hblock : StrictMono block :=
    FiniteIndex.blockMap_strictMono hsource htarget vertex hvertex
  have huniv (v : Fin N) :
      (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm
        ⟨v, Finset.mem_univ v⟩).val = v.val := by
    rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
  have hblock_val (p : Fin (2 * (2 * S.card))) :
      (block p).val =
        4 * (vertex (orderedQuarticLegEquiv S.card p).1).val +
          (orderedQuarticLegEquiv S.card p).2.val := by
    have h := FiniteIndex.eq_cast_mul_add_blockEquiv htarget (block p)
    have hv := congrArg Fin.val h
    have hmap : FiniteIndex.blockEquiv htarget (block p) =
        (vertex (orderedQuarticLegEquiv S.card p).1,
          (orderedQuarticLegEquiv S.card p).2) := by
      change FiniteIndex.blockEquiv htarget
        (FiniteIndex.blockMap hsource htarget vertex p) = _
      exact FiniteIndex.blockEquiv_blockMap hsource htarget vertex p
    rw [hmap] at hv
    simpa only [Fin.val_cast, Fin.val_mk, Prod.fst, Prod.snd,
      Nat.mul_comm] using hv
  have hslot_val (p : Fin (2 * (2 * S.card))) :
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order p))).val =
      2 * E + (orderedQuarticLegEquiv S.card p).2.val +
        4 * (vertex (orderedQuarticLegEquiv S.card p).1).val := by
    let leg := orderedQuarticLegEquiv S.card p
    have hleg : orderedLegToDiagramLeg S order p =
        (quarticLegEquiv S).symm (order leg.1, leg.2) := by
      simp [orderedLegToDiagramLeg, leg, Prod.map]
    rw [hleg]
    have hright := externalInsertionSlotLegSplitting_right_interaction
      (E := E) (Finset.subset_univ T) (order leg.1) leg.2
    rw [hright]
    change (externalInsertionInteractionLeg (E := E)
      ⟨(order leg.1).1, Finset.mem_univ _⟩ leg.2).val = _
    rw [externalInsertionInteractionLeg_val]
    rw [huniv]
    rfl
  intro p q hpq
  have hp := hslot_val p
  have hq := hslot_val q
  have hbp := hblock_val p
  have hbq := hblock_val q
  have hh := hblock hpq
  change
    (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
      (Sum.inr (orderedLegToDiagramLeg S order p))).val <
    (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
      (Sum.inr (orderedLegToDiagramLeg S order q))).val
  omega

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
  change (externalInsertionInteractionLeg (E := E)
      (⟨(order w).1, Finset.mem_univ _⟩ :
        ↥(Finset.univ : Finset (Fin N))) k).val <
      (externalInsertionInteractionLeg (E := E)
      (⟨v.1, Finset.mem_univ _⟩ :
        ↥(Finset.univ : Finset (Fin N))) l).val ↔
    (order w).1 < v.1
  simp only [externalInsertionInteractionLeg_val]
  have huniv (x : Fin N) :
      (((Finset.univ : Finset (Fin N)).orderIsoOfFin rfl).symm
        ⟨x, Finset.mem_univ x⟩).val = x.val := by
    rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
  rw [huniv, huniv]
  have hne : (order w).1 ≠ v.1 := by
    intro h
    have hw : (order w).1 ∉ T := (Finset.mem_sdiff.mp (order w).2).2
    exact hw (h.symm ▸ v.2)
  have hk := k.isLt
  have hl := l.isLt
  constructor <;> intro h <;> omega

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
      have hzero :
          (∑ j : Fin (2 * (2 * S.card)),
            if externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inr (orderedLegToDiagramLeg S order j)) <
              externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
                (Sum.inl (externalInsertionExternalLeg E T e))
              then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        let vl := orderedQuarticLegEquiv S.card j
        have hj : (orderedQuarticLegEquiv S.card).symm vl = j := by simp [vl]
        rw [← hj]
        exact ite_eq_right
          (externalInsertionSlotLegSplitting_fixedRight_not_lt_leftExternal
            (E := E) T e vl.1 vl.2)
      change 2 ∣ (∑ j : Fin (2 * (2 * S.card)),
        if externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inr (orderedLegToDiagramLeg S order j)) <
            externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
              (Sum.inl (externalInsertionExternalLeg E T e))
          then 1 else 0)
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
      by_cases hlt : externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
          (Sum.inr (orderedLegToDiagramLeg S order
            ((orderedQuarticLegEquiv S.card).symm wk))) <
          externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inr (v, l))))
      · have horder := hiff'.mp hlt
        simpa [horder] using hlt
      · have horder : ¬ (order wk.1).1 < v.1 := fun h => hlt (hiff'.mpr h)
        simpa [horder] using hlt

end Common
end SecondQuantization
