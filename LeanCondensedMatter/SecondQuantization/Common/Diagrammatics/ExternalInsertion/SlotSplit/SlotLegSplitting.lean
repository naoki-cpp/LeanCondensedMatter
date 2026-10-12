import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.Diagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ExternalInsertionMixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Diagram
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

/-- The true mixed-order partner of any vacuum-complement leg in an assembled
diagram is the image of that leg's partner in the vacuum pairing. -/
theorem ExternalInsertionDiagram.ofSlotSplit_partner_right_mixedPosition
    {ExternalLabel InternalLabel : Type*} {E N : ℕ} (T : Finset (Fin N))
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N
      ((Finset.univ : Finset (Fin N)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ)
    (v : ↥((Finset.univ : Finset (Fin N)) \ T)) (l : Fin 4) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let split :=
      (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)).trans
        (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
    let d := ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    (d.pairingInMixedOrder externalTime σ).partner
        (externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (Sum.inr (⟨v.1, Finset.mem_univ _⟩, l))) =
      split (Sum.inr (vac.pairing.partner ((quarticLegEquiv S).symm (v, l)))) := by
  intro S split d
  have hpos := externalInsertionSlotLegSplitting_right_mixedPosition
    T externalTime σ v l
  change split (Sum.inr ((quarticLegEquiv S).symm (v, l))) = _ at hpos
  rw [← hpos]
  let slot := externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)
  let fixed := externalInsertionMixedTimeAmbientPositionEquiv externalTime σ
  change ((Pairing.ofSplit slot ext.pairing vac.pairing).transport fixed).partner
      (split (Sum.inr ((quarticLegEquiv S).symm (v, l)))) =
    split (Sum.inr (vac.pairing.partner ((quarticLegEquiv S).symm (v, l))))
  rw [PairingOn.transport_partner]
  simp only [split, fixed, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [Pairing.ofSplit_partner_inr]

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
        externalInsertionMixedTimeOrderedAtomicLegPosition
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
          (externalInsertionMixedTimeOrderedAtomicLegEquiv
            (Fin.elim0 : Fin 0 → ℝ) (σ ∘ f) p))) := by
    apply externalInsertionMixedTimeOrderedAtomicLegPosition_map_strictMono
    · intro a b _
      exact a.elim0
    · exact (S.orderIsoOfFin rfl).strictMono
  have hposition (q : Fin (2 * (2 * S.card))) :
      splitting (Sum.inr q) =
        externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
          (orderedExternalInsertionLegMap
            (Fin.elim0 : Fin 0 → Fin (2 * E)) f
            (externalInsertionMixedTimeOrderedAtomicLegEquiv
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
  rw [hposition p, hposition q]
  exact hembed (hlocal hpq)

/-- Under the increasing vacuum vertex enumeration, the actual mixed-time
partner of an assembled vacuum leg is the image of its partner in the vacuum
diagram's ordered pairing. The explicit vertex-order transport does not assume
the intrinsic quartic vertex enumeration is increasing. -/
theorem ExternalInsertionDiagram.ofSlotSplit_partner_right_orderedLeg
    {ExternalLabel InternalLabel : Type*} {E N : ℕ} (T : Finset (Fin N))
    (ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T)
    (vac : QuarticDiagram InternalLabel N
      ((Finset.univ : Finset (Fin N)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin N → ℝ)
    (p : Fin (2 * (2 * ((Finset.univ : Finset (Fin N)) \ T).card))) :
    let S := (Finset.univ : Finset (Fin N)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let d := ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    let embed : Fin (2 * (2 * S.card)) → Fin (2 * (2 * N + E)) := fun q =>
      externalInsertionMixedTimeOrderedAtomicLegPosition externalTime σ
        (Sum.inr
          (⟨(order (orderedQuarticLegEquiv S.card q).1).1, Finset.mem_univ _⟩,
            (orderedQuarticLegEquiv S.card q).2))
    (d.pairingInMixedOrder externalTime σ).partner (embed p) =
      embed ((vac.pairingInOrder order).partner p) := by
  intro S order d embed
  let leg := orderedLegToDiagramLeg S order
  let split :=
    (externalInsertionSlotLegSplitting (E := E) (Finset.subset_univ T)).trans
      (externalInsertionMixedTimeAmbientPositionEquiv externalTime σ).symm
  have hordered (q : Fin (2 * (2 * S.card))) :
      leg q = (quarticLegEquiv S).symm
        (order (orderedQuarticLegEquiv S.card q).1,
          (orderedQuarticLegEquiv S.card q).2) := by
    simp only [leg, orderedLegToDiagramLeg, Equiv.trans_apply,
      Equiv.prodCongr_apply]
    cases orderedQuarticLegEquiv S.card q with
    | mk v l => rfl
  have hpos (q : Fin (2 * (2 * S.card))) :
      split (Sum.inr (leg q)) = embed q := by
    rw [hordered]
    exact externalInsertionSlotLegSplitting_right_mixedPosition T externalTime σ
      (order (orderedQuarticLegEquiv S.card q).1)
      (orderedQuarticLegEquiv S.card q).2
  have hpartner (q : Fin (2 * (2 * S.card))) :
      vac.pairing.partner (leg q) =
        leg ((vac.pairingInOrder order).partner q) := by
    change vac.pairing.partner (leg q) =
      leg ((vac.pairing.transport leg).partner q)
    rw [PairingOn.transport_partner, Equiv.apply_symm_apply]
  calc
    (d.pairingInMixedOrder externalTime σ).partner (embed p) =
        (d.pairingInMixedOrder externalTime σ).partner
          (split (Sum.inr (leg p))) := by rw [hpos]
    _ = split (Sum.inr (vac.pairing.partner (leg p))) := by
      rw [hpos, hordered]
      exact ExternalInsertionDiagram.ofSlotSplit_partner_right_mixedPosition
        T ext vac externalTime σ
        (order (orderedQuarticLegEquiv S.card p).1)
        (orderedQuarticLegEquiv S.card p).2
    _ = split (Sum.inr (leg ((vac.pairingInOrder order).partner p))) := by
      rw [hpartner]
    _ = embed ((vac.pairingInOrder order).partner p) :=
      hpos ((vac.pairingInOrder order).partner p)

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
