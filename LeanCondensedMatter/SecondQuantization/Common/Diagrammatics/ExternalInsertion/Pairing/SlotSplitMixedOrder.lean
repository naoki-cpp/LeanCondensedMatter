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
  have hleft (p : Fin (2 * (2 * T.card + E))) :
      splitting (Sum.inl p) = fixed.symm (slot (Sum.inl p)) := rfl
  have hright (q : Fin (2 * (2 * S.card))) :
      splitting (Sum.inr q) = fixed.symm (slot (Sum.inr (leg q))) := rfl
  have hvac (q : Fin (2 * (2 * S.card))) :
      vac.pairing.partner (leg q) =
        leg ((vac.pairingInOrder order).partner q) := by
    change vac.pairing.partner (leg q) =
      leg ((vac.pairing.transport leg).partner q)
    rw [PairingOn.transport_partner, Equiv.apply_symm_apply]
  have hfixed :
      (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).pairingInMixedOrder
          externalTime σ =
        (Pairing.ofSplit slot ext.pairing vac.pairing).transport fixed := rfl
  rw [hfixed]
  refine PairingOn.ext (Equiv.ext fun i => ?_)
  obtain ⟨u, rfl⟩ := splitting.surjective i
  cases u with
  | inl p =>
      rw [Pairing.ofSplit_partner_inl, hleft, hleft,
        PairingOn.transport_partner, Equiv.apply_symm_apply,
        Pairing.ofSplit_partner_inl]
  | inr q =>
      rw [Pairing.ofSplit_partner_inr, hright, hright,
        PairingOn.transport_partner, Equiv.apply_symm_apply,
        Pairing.ofSplit_partner_inr, hvac]

end Common
end SecondQuantization
