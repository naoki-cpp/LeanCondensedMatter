import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentPairProduct
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints

set_option linter.style.header false

/-!
# Component pairs and restricted two-point pairings

A normalized ambient pair assigned to one full component may be transported through the component
leg equivalence and then normalized in the restricted pairing.  Although the leg equivalence need
not preserve the ambient linear order, it preserves partner orbits.  This module proves that the
resulting map is an equivalence and specializes it to the canonical external and vacuum component
restrictions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- Recovering the pair containing one of its endpoints recovers the original normalized pair. -/
private theorem pairing_positionToPairEndpoint_fst_pairEndpoint {n : ℕ}
    (pairing : Pairing n) (pr : pairing.NormalizedPair) (k : Fin 2) :
    (pairing.positionToPairEndpoint (pairing.pairEndpoint (pr, k))).1 = pr := by
  exact congrArg Prod.fst (pairing.pairEndpointEquiv.left_inv (pr, k))

/-- Flattened legs belonging to one full component of a two-point diagram. -/
abbrev TwoPointDiagram.ComponentLeg {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :=
  {leg : Fin (2 * (2 * S.card + 1)) //
    d.legInComponent (B : Finset (TwoPointVertex S)) leg}

/-- The normalized ambient pair containing a component leg is assigned to that component. -/
private theorem TwoPointDiagram.pairComponent_positionToPairEndpoint_eq
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (leg : d.ComponentLeg B) :
    d.pairComponent (d.pairing.positionToPairEndpoint leg.1).1 = B := by
  generalize hxdef : d.pairing.positionToPairEndpoint leg.1 = x
  rcases x with ⟨pr, k⟩
  have hx : d.pairing.pairEndpoint (pr, k) = leg.1 := by
    have h := d.pairing.pairEndpointEquiv.right_inv leg.1
    change d.pairing.pairEndpoint
      (d.pairing.positionToPairEndpoint leg.1) = leg.1 at h
    rw [hxdef] at h
    exact h
  apply Subtype.ext
  change d.componentBlock (twoPointVertexOfLeg pr.1.1) =
    (B : Finset (TwoPointVertex S))
  fin_cases k
  · have hfirst : pr.1.1 = leg.1 := by simpa using hx
    simpa [TwoPointDiagram.legInComponent, hfirst] using leg.2
  · have hsecond : pr.1.2 = leg.1 := by simpa using hx
    have hsecondComponent :
        d.componentBlock (twoPointVertexOfLeg pr.1.2) =
          (B : Finset (TwoPointVertex S)) := by
      simpa [TwoPointDiagram.legInComponent, hsecond] using leg.2
    exact (d.componentBlock_second_eq_first_of_normalizedPair pr).symm.trans
      hsecondComponent

/-- The two selected endpoints of component pairs are equivalent to all flattened legs of the
component. -/
noncomputable def TwoPointDiagram.componentPairEndpointEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) :
    d.ComponentPair B × Fin 2 ≃ d.ComponentLeg B where
  toFun x := by
    rcases x with ⟨pr, k⟩
    refine ⟨d.pairing.pairEndpoint (pr.1, k), ?_⟩
    fin_cases k
    · simpa using d.componentPair_first_legInComponent B pr
    · simpa using d.componentPair_second_legInComponent B pr
  invFun leg :=
    let x := d.pairing.positionToPairEndpoint leg.1
    (⟨x.1, d.pairComponent_positionToPairEndpoint_eq B leg⟩, x.2)
  left_inv x := by
    rcases x with ⟨pr, k⟩
    have h := d.pairing.pairEndpointEquiv.left_inv (pr.1, k)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · change (d.pairing.positionToPairEndpoint
          (d.pairing.pairEndpoint (pr.1, k))).2 = k
      exact congrArg Prod.snd h
  right_inv leg := by
    apply Subtype.ext
    exact d.pairing.pairEndpointEquiv.right_inv leg.1

@[simp]
theorem TwoPointDiagram.componentPairEndpointEquiv_apply_zero
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    (d.componentPairEndpointEquiv B (pr, 0)).1 = pr.1.1.1 := by
  rfl

@[simp]
theorem TwoPointDiagram.componentPairEndpointEquiv_apply_one
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    (d.componentPairEndpointEquiv B (pr, 1)).1 = pr.1.1.2 := by
  rfl

/-- On component endpoints, the restricted partner exchanges endpoint zero and endpoint one of the
same normalized ambient pair. -/
theorem TwoPointDiagram.restrictedPartner_componentPairEndpoint_zero
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (pr : d.ComponentPair B) :
    d.restrictedPartner (B : Finset (TwoPointVertex S))
        (d.componentPairEndpointEquiv B (pr, 0)) =
      d.componentPairEndpointEquiv B (pr, 1) := by
  apply Subtype.ext
  rw [d.restrictedPartner_val]
  exact ((d.pairing.mem_pairs_iff pr.1.1.1 pr.1.1.2).1 pr.1.2).2

/-- Transport a component pair through a component-leg equivalence and normalize it in the local
restricted pairing. -/
noncomputable def TwoPointDiagram.componentPairToRestricted
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n) :
    d.ComponentPair B → localPairing.NormalizedPair :=
  fun pr =>
    (localPairing.positionToPairEndpoint
      (e (d.componentPairEndpointEquiv B (pr, 0)))).1

/-- The component-pair and local restricted-pair types have the same cardinality whenever their leg
sets are equivalent. -/
theorem TwoPointDiagram.card_componentPair_eq_restrictedNormalizedPair
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n) :
    Fintype.card (d.ComponentPair B) = Fintype.card localPairing.NormalizedPair := by
  classical
  letI : Fintype (d.ComponentLeg B) := Fintype.ofFinite _
  have h : Fintype.card (d.ComponentPair B × Fin 2) =
      Fintype.card (localPairing.NormalizedPair × Fin 2) :=
    (Fintype.card_congr (d.componentPairEndpointEquiv B)).trans
      ((Fintype.card_congr e).trans
        (Fintype.card_congr localPairing.pairEndpointEquiv).symm)
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- The component-pair transport is surjective when the local partner is the transported restricted
partner. -/
theorem TwoPointDiagram.componentPairToRestricted_surjective
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n)
    (hpartner : ∀ leg,
      localPairing.partner (e leg) =
        e (d.restrictedPartner (B : Finset (TwoPointVertex S)) leg)) :
    Function.Surjective (d.componentPairToRestricted B e localPairing) := by
  intro localPr
  let componentLeg : d.ComponentLeg B := e.symm localPr.1.1
  let x := (d.componentPairEndpointEquiv B).symm componentLeg
  refine ⟨x.1, ?_⟩
  have hx : d.componentPairEndpointEquiv B x = componentLeg :=
    (d.componentPairEndpointEquiv B).apply_symm_apply componentLeg
  rcases x with ⟨pr, k⟩
  fin_cases k
  · have hfirst :
        e (d.componentPairEndpointEquiv B (pr, 0)) = localPr.1.1 := by
      calc
        e (d.componentPairEndpointEquiv B (pr, 0)) = e componentLeg :=
          congrArg e (by simpa using hx)
        _ = localPr.1.1 := e.apply_symm_apply localPr.1.1
    unfold TwoPointDiagram.componentPairToRestricted
    rw [hfirst]
    exact pairing_positionToPairEndpoint_fst_pairEndpoint localPairing localPr 0
  · have hsecond :
        e (d.componentPairEndpointEquiv B (pr, 1)) = localPr.1.1 := by
      calc
        e (d.componentPairEndpointEquiv B (pr, 1)) = e componentLeg :=
          congrArg e (by simpa using hx)
        _ = localPr.1.1 := e.apply_symm_apply localPr.1.1
    have hlocalPartner :
        localPairing.partner
            (e (d.componentPairEndpointEquiv B (pr, 0))) = localPr.1.1 := by
      rw [hpartner,
        d.restrictedPartner_componentPairEndpoint_zero B pr,
        hsecond]
    have hpair :=
      (localPairing.mem_pairs_iff localPr.1.1 localPr.1.2).1 localPr.2
    have hfirst :
        e (d.componentPairEndpointEquiv B (pr, 0)) = localPr.1.2 := by
      calc
        e (d.componentPairEndpointEquiv B (pr, 0)) =
            localPairing.partner
              (localPairing.partner
                (e (d.componentPairEndpointEquiv B (pr, 0)))) := by
          rw [localPairing.partner_partner]
        _ = localPairing.partner localPr.1.1 := by rw [hlocalPartner]
        _ = localPr.1.2 := hpair.2
    unfold TwoPointDiagram.componentPairToRestricted
    rw [hfirst]
    exact pairing_positionToPairEndpoint_fst_pairEndpoint localPairing localPr 1

/-- Component pairs are equivalent to the normalized pairs of any restricted pairing obtained by
transporting the restricted partner through the supplied leg equivalence. -/
noncomputable def TwoPointDiagram.componentPairRestrictedEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n)
    (hpartner : ∀ leg,
      localPairing.partner (e leg) =
        e (d.restrictedPartner (B : Finset (TwoPointVertex S)) leg)) :
    d.ComponentPair B ≃ localPairing.NormalizedPair :=
  Equiv.ofBijective (d.componentPairToRestricted B e localPairing)
    ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨d.componentPairToRestricted_surjective B e localPairing hpartner,
        d.card_componentPair_eq_restrictedNormalizedPair B e localPairing⟩)

/-- Ambient pairs in the common external component are equivalent to normalized pairs of the
restricted external pairing. -/
noncomputable def TwoPointDiagram.externalComponentPairEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    d.ComponentPair d.externalComponentPart ≃
      d.restrictedExternalPairing.NormalizedPair :=
  d.componentPairRestrictedEquiv d.externalComponentPart d.externalBlockLegEquiv
    d.restrictedExternalPairing
    d.restrictedExternalPairing_partner_externalBlockLegEquiv

/-- Ambient pairs in a vacuum component are equivalent to normalized pairs of the corresponding
restricted quartic pairing. -/
noncomputable def TwoPointDiagram.vacuumComponentPairEquiv
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B) :
    d.ComponentPair B ≃ (d.restrictedVacuumPairing B hVac).NormalizedPair :=
  d.componentPairRestrictedEquiv B (d.vacuumBlockLegEquiv B hVac)
    (d.restrictedVacuumPairing B hVac)
    (d.restrictedVacuumPairing_partner_vacuumBlockLegEquiv B hVac)

/-- Reindex a product over external-component ambient pairs as a product over the restricted
external pairing. -/
theorem TwoPointDiagram.prod_externalComponentPairs_comp_equiv
    {M : Type*} [CommMonoid M] {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (F : d.restrictedExternalPairing.NormalizedPair → M) :
    (∏ pr : d.ComponentPair d.externalComponentPart,
      F (d.externalComponentPairEquiv pr)) =
      ∏ pr : d.restrictedExternalPairing.NormalizedPair, F pr :=
  Equiv.prod_comp d.externalComponentPairEquiv F

/-- Reindex a product over one vacuum component's ambient pairs as a product over the restricted
vacuum pairing. -/
theorem TwoPointDiagram.prod_vacuumComponentPairs_comp_equiv
    {M : Type*} [CommMonoid M] {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (F : (d.restrictedVacuumPairing B hVac).NormalizedPair → M) :
    (∏ pr : d.ComponentPair B, F (d.vacuumComponentPairEquiv B hVac pr)) =
      ∏ pr : (d.restrictedVacuumPairing B hVac).NormalizedPair, F pr :=
  Equiv.prod_comp (d.vacuumComponentPairEquiv B hVac) F

end Common
end SecondQuantization
