import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Combinatorics.FiniteIndex.Block
import LeanCondensedMatter.Combinatorics.Common.FintypeProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.Split
import LeanCondensedMatter.Combinatorics.SubsetSplit

set_option linter.style.header false

/-!
# Slot splitting for arbitrary external-insertion diagrams

A subset `T` of interaction vertices divides the ambient legs into two sectors: all external
insertions together with the four legs of vertices in `T`, and the four legs of vertices in
`S \ T`.

A pairing that does not cross this split is equivalent to an external-insertion diagram on `T`
and an ordinary quartic diagram on the complementary slots. Connectivity is deliberately absent
from this layer; later consumers choose `T` from externally supported components.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The ambient external-insertion legs presented as the legs of `T`, including every external
leg, together with the quartic legs of `S \ T`. -/
noncomputable def externalInsertionSlotLegSplitting
    {S T : Finset (Fin N)} (h : T ⊆ S) :
    Combinatorics.PositionSplitting
      (2 * T.card + E)
      (2 * (S \ T).card)
      (2 * S.card + E) :=
  (Equiv.sumCongr (externalInsertionLegEquiv E T) (quarticLegEquiv (S \ T))).trans
    (((Equiv.sumAssoc (Fin (2 * E)) (↥T × Fin 4) (↥(S \ T) × Fin 4)).trans
      (Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
        ((Equiv.sumProdDistrib (↥T) (↥(S \ T)) (Fin 4)).symm.trans
          (Equiv.prodCongr (Combinatorics.subsetSumSdiffEquiv h) (Equiv.refl (Fin 4)))))).trans
      (externalInsertionLegEquiv E S).symm)

/-- External legs land on the left side unchanged. -/
@[simp]
theorem externalInsertionSlotLegSplitting_external
    {S T : Finset (Fin N)} (h : T ⊆ S) (e : Fin (2 * E)) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inl e))) =
      (externalInsertionLegEquiv E S).symm (Sum.inl e) := by
  simp [externalInsertionSlotLegSplitting]

/-- A left interaction leg lands on the corresponding ambient interaction leg. -/
@[simp]
theorem externalInsertionSlotLegSplitting_left_interaction
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥T) (l : Fin 4) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inr (v, l)))) =
      (externalInsertionLegEquiv E S).symm
        (Sum.inr (⟨v.1, h v.2⟩, l)) := by
  simp [externalInsertionSlotLegSplitting]

/-- A right quartic leg lands on the corresponding ambient interaction leg. -/
@[simp]
theorem externalInsertionSlotLegSplitting_right_interaction
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (v : ↥(S \ T)) (l : Fin 4) :
    externalInsertionSlotLegSplitting (E := E) h
        (Sum.inr ((quarticLegEquiv (S \ T)).symm (v, l))) =
      (externalInsertionLegEquiv E S).symm
        (Sum.inr (⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, l)) := by
  simp [externalInsertionSlotLegSplitting]

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
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
      rw [hiff]

/-- Reconstruct an external-insertion diagram from an external-bearing piece and a quartic
complementary piece. -/
noncomputable def ExternalInsertionDiagram.ofSlotSplit
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N S where
  externalLabel := ext.externalLabel
  vertexLabel v :=
    if hv : (v : Fin N) ∈ T then ext.vertexLabel ⟨v, hv⟩
    else vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩
  pairing := Pairing.ofSplit (externalInsertionSlotLegSplitting (E := E) h)
    ext.pairing vac.pairing

@[simp]
theorem ExternalInsertionDiagram.ofSlotSplit_externalLabel
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) (e : Fin (2 * E)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).externalLabel e =
      ext.externalLabel e := rfl

@[simp]
theorem ExternalInsertionDiagram.ofSlotSplit_pairing
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing =
      Pairing.ofSplit (externalInsertionSlotLegSplitting (E := E) h)
        ext.pairing vac.pairing := rfl

theorem ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (v : ↥S) (hv : (v : Fin N) ∈ T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v =
      ext.vertexLabel ⟨v, hv⟩ := dite_eq_left hv

theorem ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (v : ↥S) (hv : (v : Fin N) ∉ T) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v =
      vac.vertexLabel ⟨v, Finset.mem_sdiff.mpr ⟨v.2, hv⟩⟩ := dite_eq_right hv


/-- Reassembling disjoint external-support and vacuum diagrams multiplies their local
interaction-vertex weights, independently of the pairings or particle statistics. -/
theorem ExternalInsertionDiagram.ofSlotSplit_vertexWeight
    {M : Type*} [CommMonoid M]
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (w : InternalLabel → M) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexWeight w =
      ext.vertexWeight w * vac.vertexWeight w := by
  classical
  unfold ExternalInsertionDiagram.vertexWeight QuarticDiagram.vertexWeight
  calc
    (∏ v : ↥S, w ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v)) =
        ∏ v : ↥T ⊕ ↥(S \ T),
          w ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel
            (subsetSumSdiffEquiv h v)) :=
      (Equiv.prod_comp (subsetSumSdiffEquiv h)
        (fun v : ↥S =>
          w ((ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexLabel v))).symm
    _ = (∏ v : ↥T, w (ext.vertexLabel v)) *
        ∏ v : ↥(S \ T), w (vac.vertexLabel v) := by
      simp only [Fintype.prod_sum_type, Finset.univ_eq_attach,
        subsetSumSdiffEquiv_inl_apply, subsetSumSdiffEquiv_inr_apply]
      congr 1
      · apply Finset.prod_congr rfl
        intro v _
        rw [ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem
          h ext vac ⟨v.1, h v.2⟩ v.2]
      · apply Finset.prod_congr rfl
        intro v _
        rw [ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem
          h ext vac ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
            (Finset.mem_sdiff.mp v.2).2]


/-- Dyson interaction signs and local vertex weights split multiplicatively along the
external-support/vacuum slot partition. This statement does not concern the fermionic
mixed-time permutation or pairing-crossing sign. -/
theorem ExternalInsertionDiagram.ofSlotSplit_dysonSign_mul_vertexWeight
    {S T : Finset (Fin N)} (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (w : InternalLabel → ℂ) :
    (-1 : ℂ) ^ S.card *
        (ExternalInsertionDiagram.ofSlotSplit h ext vac).vertexWeight w =
      ((-1 : ℂ) ^ T.card * ext.vertexWeight w) *
        ((-1 : ℂ) ^ (S \ T).card * vac.vertexWeight w) := by
  classical
  have hcard : S.card = T.card + (S \ T).card := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using
      (Fintype.card_congr (subsetSumSdiffEquiv h)).symm
  rw [hcard, pow_add, ExternalInsertionDiagram.ofSlotSplit_vertexWeight]
  ring


section Decompose

variable {S T : Finset (Fin N)}

/-- The external-bearing piece of a diagram whose pairing is split by the chosen interaction slots. -/
noncomputable def ExternalInsertionDiagram.slotSplitExternal
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N T where
  externalLabel := d.externalLabel
  vertexLabel v := d.vertexLabel ⟨v.1, h v.2⟩
  pairing := d.pairing.splitLeft (externalInsertionSlotLegSplitting (E := E) h) hd

/-- The complementary vacuum piece as an ordinary quartic diagram. -/
noncomputable def ExternalInsertionDiagram.slotSplitVacuum
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    QuarticDiagram InternalLabel N (S \ T) where
  vertexLabel v := d.vertexLabel ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩
  pairing := d.pairing.splitRight (externalInsertionSlotLegSplitting (E := E) h) hd

/-- Taking a split diagram apart and reassembling it returns the original diagram. -/
theorem ExternalInsertionDiagram.ofSlotSplit_slotSplit
    (h : T ⊆ S)
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (hd : d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)) :
    ExternalInsertionDiagram.ofSlotSplit h
        (d.slotSplitExternal h hd) (d.slotSplitVacuum h hd) = d := by
  refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
  · by_cases hv : (v : Fin N) ∈ T
    · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem h _ _ v hv
    · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem h _ _ v hv
  · exact Pairing.ofSplit_splitLeft_splitRight
      (externalInsertionSlotLegSplitting (E := E) h) hd

/-- Reassembling and reading off the external-bearing piece returns that piece. -/
theorem ExternalInsertionDiagram.slotSplitExternal_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing.IsSplit
      (externalInsertionSlotLegSplitting (E := E) h)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).slotSplitExternal h hd = ext := by
  refine ExternalInsertionDiagram.ext rfl (funext fun v => ?_) ?_
  · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_mem h ext vac
      ⟨v.1, h v.2⟩ v.2
  · exact Pairing.splitLeft_ofSplit
      (externalInsertionSlotLegSplitting (E := E) h) ext.pairing vac.pairing

/-- Reassembling and reading off the quartic complementary piece returns that piece. -/
theorem ExternalInsertionDiagram.slotSplitVacuum_ofSlotSplit
    (h : T ⊆ S)
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N (S \ T))
    (hd : (ExternalInsertionDiagram.ofSlotSplit h ext vac).pairing.IsSplit
      (externalInsertionSlotLegSplitting (E := E) h)) :
    (ExternalInsertionDiagram.ofSlotSplit h ext vac).slotSplitVacuum h hd = vac := by
  refine QuarticDiagram.ext (funext fun v => ?_) ?_
  · exact ExternalInsertionDiagram.ofSlotSplit_vertexLabel_of_not_mem h ext vac
      ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ (Finset.mem_sdiff.mp v.2).2
  · exact Pairing.splitRight_ofSplit
      (externalInsertionSlotLegSplitting (E := E) h) ext.pairing vac.pairing

/-- Diagrams split by a chosen interaction-slot divide are exactly independent external-insertion
and quartic pieces. -/
noncomputable def ExternalInsertionDiagram.slotSplitEquiv
    (h : T ⊆ S) :
    {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
      d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)} ≃
      ExternalInsertionDiagram ExternalLabel InternalLabel E N T ×
        QuarticDiagram InternalLabel N (S \ T) where
  toFun d := (d.1.slotSplitExternal h d.2, d.1.slotSplitVacuum h d.2)
  invFun p :=
    ⟨ExternalInsertionDiagram.ofSlotSplit h p.1 p.2,
      Pairing.isSplit_ofSplit _ _ _⟩
  left_inv d := Subtype.ext (ExternalInsertionDiagram.ofSlotSplit_slotSplit h d.1 d.2)
  right_inv p := by
    obtain ⟨ext, vac⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨ExternalInsertionDiagram.slotSplitExternal_ofSlotSplit h ext vac _,
      ExternalInsertionDiagram.slotSplitVacuum_ofSlotSplit h ext vac _⟩

open Classical in
/-- Summing over split diagrams is summing independently over the external-insertion and quartic
pieces. -/
theorem ExternalInsertionDiagram.sum_slotSplit
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (h : T ⊆ S) {M : Type*} [AddCommMonoid M]
    (F : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
        d.pairing.IsSplit (externalInsertionSlotLegSplitting (E := E) h)}, F d.1) =
      ∑ ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T,
        ∑ vac : QuarticDiagram InternalLabel N (S \ T),
          F (ExternalInsertionDiagram.ofSlotSplit h ext vac) := by
  rw [← Equiv.sum_comp (ExternalInsertionDiagram.slotSplitEquiv h).symm (fun d => F d.1),
    Fintype.sum_prod_type]
  rfl

end Decompose

end Common
end SecondQuantization
