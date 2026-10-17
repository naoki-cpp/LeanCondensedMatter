import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.IntervalBlock
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Attaching two new external legs to a cut interval

An intermediate region has two distinguished, interval-facing ends of
separating propagators. Every other incident leg belongs to the invariant
interior pairing. This module installs two new external legs, pairs each
with the corresponding boundary end, and retains the original pairing
on all interior propagators.

The construction is for a pair of separating cuts. A proof that a resulting
block is 1PI requires that the cuts be consecutive; a general interval may
contain additional separating propagators.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- A cut has exactly one endpoint incident to the given interval. -/
def TwoPointDiagram.HasIntervalBoundaryEndpoint
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later cut : Fin (2 * (2 * S.card + 1))) : Prop :=
  (twoPointVertexOfLeg cut ∈ d.verticesBetweenCuts earlier later ∧
      twoPointVertexOfLeg (d.pairing.partner cut) ∉ d.verticesBetweenCuts earlier later) ∨
    (twoPointVertexOfLeg (d.pairing.partner cut) ∈ d.verticesBetweenCuts earlier later ∧
      twoPointVertexOfLeg cut ∉ d.verticesBetweenCuts earlier later)

/-- Distinguish the two interval-facing boundary legs by the new external
vertex to which they will be paired. -/
noncomputable def TwoPointDiagram.intervalBoundaryFacingLeg
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (e : Fin 2) : Fin (2 * (2 * S.card + 1)) :=
  if e = 0 then d.intervalFacingLeg earlier later earlier
  else d.intervalFacingLeg earlier later later

@[simp]
theorem TwoPointDiagram.intervalBoundaryFacingLeg_zero
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    d.intervalBoundaryFacingLeg earlier later 0 =
      d.intervalFacingLeg earlier later earlier := by
  simp [intervalBoundaryFacingLeg]

@[simp]
theorem TwoPointDiagram.intervalBoundaryFacingLeg_one
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1))) :
    d.intervalBoundaryFacingLeg earlier later 1 =
      d.intervalFacingLeg earlier later later := by
  simp [intervalBoundaryFacingLeg]

/-- Different boundary propagators give an injective choice of the two
incident boundary legs. -/
theorem TwoPointDiagram.intervalBoundaryFacingLeg_injective
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    Function.Injective (d.intervalBoundaryFacingLeg earlier later) := by
  intro i j hij
  have hdistinct := d.intervalFacingLeg_ne_of_pair_ne earlier later hne hpne
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (hdistinct (by simpa using hij))
  · exact False.elim (hdistinct (by simpa using hij.symm))
  · rfl

/-- The interaction legs of an interval consist of two boundary ends and
the partner-invariant subtype of interior legs. The two boundary ends
are distinguished but retain their original ambient identities. -/
noncomputable def TwoPointDiagram.intervalBoundaryInteriorLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    (Fin 2 ⊕ {leg : Fin (2 * (2 * S.card + 1)) //
      d.IsInteriorLeg earlier later leg}) ≃
      {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later} := by
  classical
  let f :
      (Fin 2 ⊕ {leg : Fin (2 * (2 * S.card + 1)) //
        d.IsInteriorLeg earlier later leg}) →
      {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later} := fun x =>
    match x with
    | Sum.inl e =>
        ⟨d.intervalBoundaryFacingLeg earlier later e, by
          fin_cases e
          · exact (d.intervalFacingLeg_mem_and_partner_not_mem
              earlier later earlier hEarlier).1
          · exact (d.intervalFacingLeg_mem_and_partner_not_mem
              earlier later later hLater).1⟩
    | Sum.inr i => ⟨i.1, i.2.1⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro a b hab
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            have hval :
                d.intervalBoundaryFacingLeg earlier later i =
                  d.intervalBoundaryFacingLeg earlier later j := by
              simpa [f] using congrArg Subtype.val hab
            exact congrArg Sum.inl
              (d.intervalBoundaryFacingLeg_injective earlier later hne hpne hval)
        | inr j =>
            have hval : d.intervalBoundaryFacingLeg earlier later i = j.1 := by
              simpa [f] using congrArg Subtype.val hab
            fin_cases i
            · exact False.elim
                ((d.isInteriorLeg_ne_intervalFacingLeg earlier later earlier j.1
                  (Or.inl rfl) j.2) (by simpa using hval.symm))
            · exact False.elim
                ((d.isInteriorLeg_ne_intervalFacingLeg earlier later later j.1
                  (Or.inr rfl) j.2) (by simpa using hval.symm))
    | inr i =>
        cases b with
        | inl j =>
            have hval : i.1 = d.intervalBoundaryFacingLeg earlier later j := by
              simpa [f] using congrArg Subtype.val hab
            fin_cases j
            · exact False.elim
                ((d.isInteriorLeg_ne_intervalFacingLeg earlier later earlier i.1
                  (Or.inl rfl) i.2) (by simpa using hval))
            · exact False.elim
                ((d.isInteriorLeg_ne_intervalFacingLeg earlier later later i.1
                  (Or.inr rfl) i.2) (by simpa using hval))
        | inr j =>
            have hval : i.1 = j.1 := by
              simpa [f] using congrArg Subtype.val hab
            exact congrArg Sum.inr (Subtype.ext hval)
  · intro x
    rcases (d.mem_verticesBetweenCuts_iff_interior_or_boundary
        earlier later x.1 hEarlier hLater).1 x.2 with hi | hleft | hright
    · exact ⟨Sum.inr ⟨x.1, hi⟩, Subtype.ext rfl⟩
    · refine ⟨Sum.inl 0, ?_⟩
      apply Subtype.ext
      simpa [f] using hleft.symm
    · refine ⟨Sum.inl 1, ?_⟩
      apply Subtype.ext
      simpa [f] using hright.symm

/-- The fixed-point-free involution pairing the two new external ends
with their two corresponding boundary legs. -/
private def intervalBoundaryPairing : PairingOn (Fin 2 ⊕ Fin 2) :=
  PairingOn.ofPartner (Equiv.sumComm (Fin 2) (Fin 2)) (by
    constructor
    · rintro (i | i) <;> rfl
    · rintro (i | i) <;> simp)

/-- Reindex the two new external ports, the two boundary ends and the
unchanged interior legs into the augmented two-point leg domain. This
equivalence also specifies the conjugation used by the pairing.
Detailed partner equations belong to a follow-up PR. -/
noncomputable def TwoPointDiagram.intervalAugmentedLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    ((Fin 2 ⊕ Fin 2) ⊕ {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}) ≃
      (Fin 2 ⊕ {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) :=
  (Equiv.sumAssoc (Fin 2) (Fin 2) {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}).trans
    (Equiv.sumCongr (Equiv.refl (Fin 2))
      (d.intervalBoundaryInteriorLegEquiv earlier later hEarlier hLater hne hpne))

/-- The interval pairing before flattening its legs: the new external
ends are paired to the old boundary ends and the remaining edges retain
their exact ambient pairing. -/
noncomputable def TwoPointDiagram.intervalAugmentedPairing
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    PairingOn (Fin 2 ⊕
      {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) := by
  exact (intervalBoundaryPairing.sumCongr
    (d.interiorPairing earlier later)).transport
      (d.intervalAugmentedLegEquiv earlier later hEarlier hLater hne hpne).symm

/-- The standard flattened block-leg space is identified with a new pair
of external legs together with all ambient legs incident to the interval. -/
noncomputable def TwoPointDiagram.intervalBlockLegEquiv
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    Fin (2 * (2 * (interactionSector (d.verticesBetweenCuts earlier later)).card + 1)) ≃
      (Fin 2 ⊕ {leg : Fin (2 * (2 * S.card + 1)) //
        twoPointVertexOfLeg leg ∈ d.verticesBetweenCuts earlier later}) :=
  (twoPointLegEquiv (interactionSector (d.verticesBetweenCuts earlier later))).trans
    (Equiv.sumCongr (Equiv.refl (Fin 2))
      (d.intervalInteractionLegEquiv earlier later hsepLater))

/-- Make a standalone two-point pairing diagram on an interval, replacing
the two cut propagators by external legs. The caller supplies labels for
these artificial boundary ports: they are not inherited from the original
physical external vertices. This applies even when the two cuts are not
consecutive (such a block need not be 1PI). -/
noncomputable def TwoPointDiagram.intervalBlock
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (boundaryLabels : Fin 2 → ExternalLabel)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    TwoPointDiagram ExternalLabel InternalLabel N
      (interactionSector (d.verticesBetweenCuts earlier later)) where
  externalLabel := boundaryLabels
  vertexLabel v := d.vertexLabel
    ⟨v.1, interactionSector_subset (d.verticesBetweenCuts earlier later) v.2⟩
  pairing :=
    (d.intervalAugmentedPairing earlier later hEarlier hLater hne hpne).transport
      (d.intervalBlockLegEquiv earlier later hsepLater)

@[simp]
theorem TwoPointDiagram.intervalBlock_externalLabel
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (boundaryLabels : Fin 2 → ExternalLabel)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later) :
    (d.intervalBlock boundaryLabels earlier later hsepLater hEarlier hLater hne hpne).externalLabel =
      boundaryLabels := rfl

section PartnerCorrespondence

variable (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (boundaryLabels : Fin 2 → ExternalLabel)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hEarlier : d.HasIntervalBoundaryEndpoint earlier later earlier)
    (hLater : d.HasIntervalBoundaryEndpoint earlier later later)
    (hne : earlier ≠ later)
    (hpne : d.pairing.partner earlier ≠ later)

/-- Each new external port is paired with its interval-facing cut endpoint. -/
theorem TwoPointDiagram.intervalAugmentedPairing_partner_external (i : Fin 2) :
    (d.intervalAugmentedPairing earlier later hEarlier hLater hne hpne).partner
      (Sum.inl i) =
        Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
          hEarlier hLater hne hpne) (Sum.inl i)) := by
  let e := d.intervalAugmentedLegEquiv earlier later hEarlier hLater hne hpne
  have hl : e (Sum.inl (Sum.inl i)) = Sum.inl i := rfl
  have hr : e (Sum.inl (Sum.inr i)) =
      Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne) (Sum.inl i)) := rfl
  rw [← hl, ← hr]
  change ((intervalBoundaryPairing.sumCongr
    (d.interiorPairing earlier later)).transport e.symm).partner
      (e (Sum.inl (Sum.inl i))) = e (Sum.inl (Sum.inr i))
  simp [PairingOn.transport_partner, intervalBoundaryPairing]; rfl

/-- The augmented pairing preserves the restricted interior partner. -/
theorem TwoPointDiagram.intervalAugmentedPairing_partner_interior
    (i : {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}) :
    (d.intervalAugmentedPairing earlier later hEarlier hLater hne hpne).partner
      (Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne) (Sum.inr i))) =
        Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
          hEarlier hLater hne hpne)
          (Sum.inr ((d.interiorPairing earlier later).partner i))) := by
  let e := d.intervalAugmentedLegEquiv earlier later hEarlier hLater hne hpne
  have hl : e (Sum.inr i) =
      Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne) (Sum.inr i)) := rfl
  have hr : e (Sum.inr ((d.interiorPairing earlier later).partner i)) =
      Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne)
        (Sum.inr ((d.interiorPairing earlier later).partner i))) := rfl
  rw [← hl, ← hr]
  change ((intervalBoundaryPairing.sumCongr
    (d.interiorPairing earlier later)).transport e.symm).partner
      (e (Sum.inr i)) = e (Sum.inr ((d.interiorPairing earlier later).partner i))
  simp [PairingOn.transport_partner]

/-- The flattened block's partner is conjugate to the augmented pairing. -/
theorem TwoPointDiagram.intervalBlock_partner_equiv
    (p : Fin (2 * (2 * (interactionSector
      (d.verticesBetweenCuts earlier later)).card + 1))) :
    (d.intervalBlockLegEquiv earlier later hsepLater)
      ((d.intervalBlock boundaryLabels earlier later hsepLater
        hEarlier hLater hne hpne).pairing.partner p) =
      (d.intervalAugmentedPairing earlier later hEarlier hLater hne hpne).partner
        ((d.intervalBlockLegEquiv earlier later hsepLater) p) := by
  simp only [TwoPointDiagram.intervalBlock, PairingOn.transport_partner,
    Equiv.apply_symm_apply]

/-- The standalone block's new external leg connects to its boundary endpoint. -/
theorem TwoPointDiagram.intervalBlock_partner_external (i : Fin 2) :
    (d.intervalBlockLegEquiv earlier later hsepLater)
      ((d.intervalBlock boundaryLabels earlier later hsepLater
        hEarlier hLater hne hpne).pairing.partner
          (twoPointExternalLeg (interactionSector
            (d.verticesBetweenCuts earlier later)) i)) =
      Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne) (Sum.inl i)) := by
  rw [d.intervalBlock_partner_equiv boundaryLabels earlier later
    hsepLater hEarlier hLater hne hpne]
  have he : (d.intervalBlockLegEquiv earlier later hsepLater)
      (twoPointExternalLeg (interactionSector
        (d.verticesBetweenCuts earlier later)) i) = Sum.inl i := by
    simp [TwoPointDiagram.intervalBlockLegEquiv, twoPointExternalLeg]
  rw [he, d.intervalAugmentedPairing_partner_external earlier later
    hEarlier hLater hne hpne]

/-- The block keeps each interior propagator's partner under leg reindexing.
`interiorPairing_partner_val` identifies it with the ambient partner. -/
theorem TwoPointDiagram.intervalBlock_partner_interior
    (i : {leg : Fin (2 * (2 * S.card + 1)) // d.IsInteriorLeg earlier later leg}) :
    (d.intervalBlockLegEquiv earlier later hsepLater)
      ((d.intervalBlock boundaryLabels earlier later hsepLater
        hEarlier hLater hne hpne).pairing.partner
          ((d.intervalBlockLegEquiv earlier later hsepLater).symm
            (Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
              hEarlier hLater hne hpne) (Sum.inr i))))) =
      Sum.inr ((d.intervalBoundaryInteriorLegEquiv earlier later
        hEarlier hLater hne hpne)
        (Sum.inr ((d.interiorPairing earlier later).partner i))) := by
  rw [d.intervalBlock_partner_equiv boundaryLabels earlier later
    hsepLater hEarlier hLater hne hpne,
    Equiv.apply_symm_apply,
    d.intervalAugmentedPairing_partner_interior earlier later
      hEarlier hLater hne hpne]

end PartnerCorrespondence

/-- Strictly nested, external-separating cuts have two distinct interval-facing
endpoints. This packages exactly the boundary data needed by `intervalBlock`
without assuming either endpoint orientation. -/
theorem TwoPointDiagram.strictCuts_boundaryData
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (hconnected : d.IsExternallyConnected)
    (earlier later : Fin (2 * (2 * S.card + 1)))
    (hstrict :
      (d.vertexGraphWithoutPropagator earlier).componentBlock (Sum.inl (0 : Fin 2)) ⊂
        (d.vertexGraphWithoutPropagator later).componentBlock (Sum.inl (0 : Fin 2)))
    (hsepEarlier : ¬ (d.vertexGraphWithoutPropagator earlier).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)))
    (hsepLater : ¬ (d.vertexGraphWithoutPropagator later).Reachable
      (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))) :
    earlier ≠ later ∧ d.pairing.partner earlier ≠ later ∧
      d.HasIntervalBoundaryEndpoint earlier later earlier ∧
      d.HasIntervalBoundaryEndpoint earlier later later := by
  have hne : earlier ≠ later := by
    intro heq
    subst later
    exact (lt_irrefl _) hstrict
  have hpne : d.pairing.partner earlier ≠ later := by
    intro heq
    subst later
    rw [d.vertexGraphWithoutPropagator_partner] at hstrict
    exact (lt_irrefl _) hstrict
  have hpne' : d.pairing.partner later ≠ earlier := by
    intro heq
    apply hpne
    have h := congrArg d.pairing.partner heq
    rw [d.pairing.partner_involutive later] at h
    exact h.symm
  exact ⟨hne, hpne,
    d.earlierCut_endpoints_opposite_interval_sides
      hconnected earlier later hstrict.le hsepEarlier hne hpne,
    d.laterCut_endpoints_opposite_interval_sides
      hconnected earlier later hstrict.le hsepLater hne.symm hpne'⟩

end Common
end SecondQuantization
