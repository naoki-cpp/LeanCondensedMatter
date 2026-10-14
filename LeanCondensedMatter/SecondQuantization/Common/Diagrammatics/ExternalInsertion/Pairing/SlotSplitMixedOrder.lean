import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SlotLegSplitting
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder

set_option linter.style.header false

/-!
# Mixed-time coherence of slot-split external-insertion diagrams

The slot partition and diagram reconstruction are independent of event times. This module relates
their legs and pairings to mixed-time positions and the increasing vertex order of the vacuum
complement. Order preservation retains its explicit local vacuum ordering hypothesis.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- The right-sector leg in a slot splitting occupies the mixed-time position
of the same actual vacuum vertex leg in the full external-insertion diagram.

The vertex here is the one given by the quartic leg equivalence of the
complementary finset; no agreement with a separately chosen sorted slot
enumeration is presumed. -/
theorem externalInsertionSlotLegSplitting_right_mixedPosition
    {E N : ℕ} (T : Finset (Fin N))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ)
    (v : ↥((Finset.univ : Finset (Fin N)) \ T)) (l : Fin 4) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let split :=
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    split (Sum.inr ((quarticLegEquiv S).symm (v, l))) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr (⟨v.1, Finset.mem_univ _⟩, l)) := by
  intro S split
  apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
  simp only [split, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [externalInsertionSlotLegSplitting_right_interaction]
  apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin N))).injective
  rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position,
    Equiv.apply_symm_apply]

/-- The increasing vertex order of the vacuum complement gives the exact
ambient mixed-time position of every ordered quartic vacuum leg. -/
theorem externalInsertionSlotLegSplitting_right_orderedMixedPosition
    {E N : ℕ} (T : Finset (Fin N))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin N)) \ T).card))) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let splitting :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    splitting (Sum.inr p) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr
          (⟨(order (orderedQuarticLegEquiv S.card p).1).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card p).2)) := by
  intro S order splitting
  have hordered :
      orderedLegToDiagramLeg S order p =
        (quarticLegEquiv S).symm
          (order (orderedQuarticLegEquiv S.card p).1,
            (orderedQuarticLegEquiv S.card p).2) := by
    simp only [orderedLegToDiagramLeg, Equiv.trans_apply, Equiv.prodCongr_apply]
    cases orderedQuarticLegEquiv S.card p with
    | mk v l => rfl
  change
    (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inr (orderedLegToDiagramLeg S order p))) = _
  rw [hordered]
  exact externalInsertionSlotLegSplitting_right_mixedPosition T externalTime σ
    (order (orderedQuarticLegEquiv S.card p).1)
    (orderedQuarticLegEquiv S.card p).2

/-- If the standalone vacuum-only mixed ordering preserves the flattened quartic-leg
order, its embedding into the full mixed-time family also preserves that order.
This separates the local vacuum time-chamber condition from arbitrary external event times. -/
theorem externalInsertionSlotLegSplitting_right_strictMono_of_localOrder
    {E N : ℕ} (T : Finset (Fin N))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin N := fun i => (S.orderIsoOfFin rfl i).1
    let splitting :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let localPosition : Fin (2 * (2 * S.card)) → Fin (2 * (2 * S.card)) :=
      fun q =>
        externalInsertionMixedTimeOrderedAtomicLegPosition (E := 0)
          (Fin.elim0 : Fin 0 → ℝ) (σ ∘ f)
          (Sum.inr
            (⟨(orderedQuarticLegEquiv S.card q).1, Finset.mem_univ _⟩,
              (orderedQuarticLegEquiv S.card q).2))
    StrictMono localPosition →
      StrictMono (fun q : Fin (2 * (2 * S.card)) => splitting (Sum.inr q)) := by
  intro S order f splitting localPosition hlocal
  have hembed : StrictMono (fun p : Fin (2 * (2 * S.card)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap
          (Fin.elim0 : Fin 0 → Fin (2 * E)) f
          (externalInsertionMixedTimeOrderedAtomicLegEquiv (E := 0)
            (Fin.elim0 : Fin 0 → ℝ) (σ ∘ f) p))) := by
    have hmap :=
      externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
        (E₁ := 0) (E₂ := E) (m := S.card) (n := N)
        (fExternal := (Fin.elim0 : Fin 0 → Fin (2 * E)))
        (fInteraction := f)
        (by
          intro a b _
          exact a.elim0)
        (S.orderIsoOfFin rfl).strictMono externalTime σ
    have hzero :
        externalTime ∘ (Fin.elim0 : Fin 0 → Fin (2 * E)) =
          (Fin.elim0 : Fin 0 → ℝ) := by
      funext a
      exact a.elim0
    simpa only [hzero, Nat.add_zero] using hmap
  have hposition (q : Fin (2 * (2 * S.card))) :
      splitting (Sum.inr q) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap
            (Fin.elim0 : Fin 0 → Fin (2 * E)) f
            (externalInsertionMixedTimeOrderedAtomicLegEquiv (E := 0)
              (Fin.elim0 : Fin 0 → ℝ) (σ ∘ f) (localPosition q))) := by
    rw [externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
    change splitting (Sum.inr q) =
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr
          (⟨(order (orderedQuarticLegEquiv S.card q).1).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card q).2))
    exact externalInsertionSlotLegSplitting_right_orderedMixedPosition
      T externalTime σ q
  intro p q hpq
  change splitting (Sum.inr p) < splitting (Sum.inr q)
  rw [hposition p, hposition q]
  exact hembed (hlocal hpq)

/-- Reassembling with the vacuum pairing transported to the increasing
complementary vertex order gives the same actual mixed-time pairing.

The right leg of the splitting is reindexed via orderedLegToDiagramLeg;
the intrinsic quartic vertex enumeration need not agree with orderIsoOfFin. -/
theorem ExternalInsertionDiagram.ofSlotSplit_pairingInMixedOrder_eq_ofSplit_orderedVacuum
    {ExternalLabel InternalLabel : Type*} {E N : ℕ} (T : Finset (Fin N))
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N
      ((Finset.univ : Finset (Fin N)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let splitting :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
        externalTime σ =
      Pairing.ofSplit splitting ext.pairing (vac.pairingInOrder order) := by
  intro S order splitting
  let slot := externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
  let fixed := externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
  let leg := orderedLegToDiagramLeg S order
  let ambient := slot.trans fixed.symm
  change (Pairing.ofSplit slot ext.pairing vac.pairing).transport fixed =
    Pairing.ofSplit splitting ext.pairing (vac.pairingInOrder order)
  calc
    _ = Pairing.ofSplit ambient ext.pairing vac.pairing := by
      rw [Pairing.ofSplit, PairingOn.transport_trans]
      rfl
    _ = _ :=
      (Pairing.ofSplit_reindex ambient ext.pairing vac.pairing
        (Equiv.refl (Fin (2 * (2 * T.card + E)))) leg).symm

/-- In increasing support-slot coordinates, the external sector's mixed-to-fixed
position map is the inverse of the standard standalone mixed-time permutation. -/
private theorem externalInsertionSupportMixedPosition_eq_standard
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    ((externalInsertionMixedTimeOrderedAtomicLegEquiv
    externalTime (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).trans
    ((Equiv.sumCongr
      (Equiv.refl (Fin (2 * E)))
      (((Equiv.subtypeUnivEquiv
        (fun i : Fin T.card => Finset.mem_univ i)).trans
        (T.orderIsoOfFin rfl).toEquiv).prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E T).symm)) =
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm := by
  classical
  let supportFixed :
      OrderedExternalInsertionLeg E T.card ≃ Fin (2 * (2 * T.card + E)) :=
    ((Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
      (((Equiv.subtypeUnivEquiv (fun i : Fin T.card => Finset.mem_univ i)).trans
        (T.orderIsoOfFin rfl).toEquiv).prodCongr (Equiv.refl (Fin 4)))).trans
      (externalInsertionLegEquiv E T).symm)
  let standardFixed :
      OrderedExternalInsertionLeg E T.card ≃ Fin (2 * (2 * T.card + E)) :=
    (externalInsertionLegEquiv E (Finset.univ : Finset (Fin T.card))).symm.trans
      (finCongr (by simp))
  have hfixed : supportFixed = standardFixed := by
    apply Equiv.ext
    intro leg
    cases leg with
    | inl e =>
        apply Fin.ext
        change (externalInsertionExternalLeg E T e).val =
          (Fin.cast (by simp)
            (externalInsertionExternalLeg E
              (Finset.univ : Finset (Fin T.card)) e)).val
        simp only [Fin.val_cast, externalInsertionExternalLeg_val]
    | inr vl =>
        rcases vl with ⟨v, l⟩
        apply Fin.ext
        change (externalInsertionInteractionLeg (E := E)
            (T.orderIsoOfFin rfl v.1) l).val =
          (Fin.cast (by simp)
            (externalInsertionInteractionLeg (E := E) v l)).val
        simp only [Fin.val_cast, externalInsertionInteractionLeg_val]
        have huniv :
            (((Finset.univ : Finset (Fin T.card)).orderIsoOfFin rfl).symm v).val =
              v.1.val := by
          rw [Finset.orderIsoOfFin_symm_apply, Fin.sort_univ, List.idxOf_finRange]
        have hT :
            (((T.orderIsoOfFin rfl).symm (T.orderIsoOfFin rfl v.1)).val) =
              v.1.val := by
          simp
        rw [huniv, hT]
  apply Equiv.ext
  intro p
  change supportFixed
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p) =
    standardFixed
      (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p)
  rw [hfixed]



/-- The external-half mixed-position embedding preserves mixed time order, because
the support slots have been enumerated increasingly. -/
theorem externalInsertionLeftMixedPosition_strictMono
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (orderedExternalInsertionLegMap (fun e => e)
          (fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)
          (externalInsertionMixedTimeOrderedAtomicLegEquiv
            externalTime (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p))) := by
  apply externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
  · exact strictMono_id
  · exact (T.orderIsoOfFin rfl).strictMono

/-- The mixed-position embedding of the external half is the mixed-order image
of the actual left leg of the assembled slot splitting. -/
theorem externalInsertionLeftMixedPosition_fixed
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (p : Fin (2 * (2 * T.card + E))) :
    let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e) f
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
              externalTime (σ ∘ f) p))) =
      externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl ((externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm p)) := by
  rw [← externalInsertionSupportMixedPosition_eq_standard T externalTime σ]
  let f : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
  let leg := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime (σ ∘ f) p
  apply (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))).injective
  rw [externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    externalInsertionMixedTimeOrderedAtomicLegEquiv_position]
  change orderedExternalInsertionLegMap (fun e => e) f leg =
    externalInsertionLegEquiv E (Finset.univ : Finset (Fin n))
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
        (Sum.inl ((externalInsertionLegEquiv E T).symm
          ((Equiv.sumCongr (Equiv.refl (Fin (2 * E)))
            (((Equiv.subtypeUnivEquiv
              (fun i : Fin T.card => Finset.mem_univ i)).trans
              (T.orderIsoOfFin rfl).toEquiv).prodCongr
                (Equiv.refl (Fin 4)))) leg))))
  cases leg with
  | inl e =>
      change Sum.inl e =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))
          (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl ((externalInsertionLegEquiv E T).symm (Sum.inl e))))
      rw [externalInsertionSlotLegSplitting_external, Equiv.apply_symm_apply]
  | inr v =>
      rcases v with ⟨v, l⟩
      change Sum.inr (⟨f v.1, Finset.mem_univ _⟩, l) =
        (externalInsertionLegEquiv E (Finset.univ : Finset (Fin n)))
          (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
            (Sum.inl ((externalInsertionLegEquiv E T).symm
              (Sum.inr ((T.orderIsoOfFin rfl v.1), l)))))
      rw [externalInsertionSlotLegSplitting_left_interaction, Equiv.apply_symm_apply]

/-- Express the assembled mixed-time pairing using the external half's own
mixed-time positions. The local pairing and its position splitting are reindexed together. -/
theorem externalInsertionOfSlotSplit_pairingInMixedOrder_eq_ofSplit_mixedExternal
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E n T)
    (vac : QuarticDiagram InternalLabel n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
        externalTime σ =
      Pairing.ofSplit
        ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (ext.pairing.transport localFixed) (vac.pairingInOrder order) := by
  intro S order localFixed split
  calc
    _ = Pairing.ofSplit split ext.pairing (vac.pairingInOrder order) :=
      ExternalInsertionDiagram.ofSlotSplit_pairingInMixedOrder_eq_ofSplit_orderedVacuum
        T ext vac externalTime σ
    _ = _ := (Pairing.ofSplit_reindex split ext.pairing
      (vac.pairingInOrder order) localFixed
      (Equiv.refl (Fin (2 * (2 * S.card))))).symm

/-- The external half of the reindexed mixed-time slot splitting is strictly
increasing. This does not assert that the original flattened external order is
preserved by the physical time ordering. -/
theorem externalInsertionLeftMixedPosition_split_strictMono
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let localFixed := (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm
    let split :=
      ((Equiv.sumCongr (Equiv.refl (Fin (2 * (2 * T.card + E))))
        (orderedLegToDiagramLeg S order)).trans
        (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T))).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    StrictMono (fun p : Fin (2 * (2 * T.card + E)) =>
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl p)) := by
  intro S order localFixed split
  have hposition (p : Fin (2 * (2 * T.card + E))) :
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
          (Sum.inl p) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap (fun e => e)
            (fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
              externalTime
              (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1) p)) := by
    apply (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).injective
    simpa only [split, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.refl_apply, Equiv.apply_symm_apply] using
        (externalInsertionLeftMixedPosition_fixed T externalTime σ p).symm
  intro a b hab
  change
    ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl a) <
      ((Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))).trans split)
        (Sum.inl b)
  rw [hposition a, hposition b]
  exact (externalInsertionLeftMixedPosition_strictMono T externalTime σ) hab


end Common
end SecondQuantization
