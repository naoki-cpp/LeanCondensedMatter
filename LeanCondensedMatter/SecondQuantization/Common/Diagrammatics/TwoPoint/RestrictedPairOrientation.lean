import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.RestrictedPairEquiv

set_option linter.style.header false

/-!
# Orientation of restricted two-point component pairs

Restricting a two-point diagram component transports partner orbits through a leg equivalence, but
that equivalence need not preserve the ambient linear order used to normalize pairs. Consequently a
normalized ambient component pair becomes either the corresponding ordered local pair or its swap.
This file records that dichotomy explicitly for generic, external, and vacuum restrictions.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The restricted normalized pair containing the transported first endpoint contains that endpoint
as either its first or second entry. -/
theorem TwoPointDiagram.componentPairToRestricted_contains_first_endpoint
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n)
    (pr : d.ComponentPair B) :
    (d.componentPairToRestricted B e localPairing pr).1.1 =
        e (d.componentPairEndpointEquiv B (pr, 0)) ∨
      (d.componentPairToRestricted B e localPairing pr).1.2 =
        e (d.componentPairEndpointEquiv B (pr, 0)) := by
  let a := e (d.componentPairEndpointEquiv B (pr, 0))
  let x := localPairing.positionToPairEndpoint a
  have hx : localPairing.pairEndpoint x = a :=
    localPairing.pairEndpointEquiv.right_inv a
  change x.1.1.1 = a ∨ x.1.1.2 = a
  rcases x with ⟨localPr, k⟩
  fin_cases k
  · left
    simpa using hx
  · right
    simpa using hx

/-- Transporting one ambient component pair to a restricted pairing preserves its two endpoints up
to swapping their normalized order. -/
theorem TwoPointDiagram.componentPairToRestricted_pair_eq_or_swap
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n)
    (hpartner : ∀ leg,
      localPairing.partner (e leg) =
        e (d.restrictedPartner (B : Finset (TwoPointVertex S)) leg))
    (pr : d.ComponentPair B) :
    (d.componentPairToRestricted B e localPairing pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 0)),
          e (d.componentPairEndpointEquiv B (pr, 1))) ∨
      (d.componentPairToRestricted B e localPairing pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 1)),
          e (d.componentPairEndpointEquiv B (pr, 0))) := by
  let localPr := d.componentPairToRestricted B e localPairing pr
  have hcontains := d.componentPairToRestricted_contains_first_endpoint B e localPairing pr
  have hab :
      localPairing.partner (e (d.componentPairEndpointEquiv B (pr, 0))) =
        e (d.componentPairEndpointEquiv B (pr, 1)) := by
    rw [hpartner, d.restrictedPartner_componentPairEndpoint_zero B pr]
  have hpair :=
    (localPairing.mem_pairs_iff localPr.1.1 localPr.1.2).1 localPr.2
  rcases hcontains with hfirst | hsecond
  · left
    apply Prod.ext
    · exact hfirst
    · calc
        localPr.1.2 = localPairing.partner localPr.1.1 := hpair.2.symm
        _ = localPairing.partner
            (e (d.componentPairEndpointEquiv B (pr, 0))) := by rw [hfirst]
        _ = e (d.componentPairEndpointEquiv B (pr, 1)) := hab
  · right
    apply Prod.ext
    · have hpartnerSecond :
          localPairing.partner localPr.1.2 = localPr.1.1 := by
        calc
          localPairing.partner localPr.1.2 =
              localPairing.partner (localPairing.partner localPr.1.1) := by
            rw [hpair.2]
          _ = localPr.1.1 := localPairing.partner_partner localPr.1.1
      calc
        localPr.1.1 = localPairing.partner localPr.1.2 := hpartnerSecond.symm
        _ = localPairing.partner
            (e (d.componentPairEndpointEquiv B (pr, 0))) := by rw [hsecond]
        _ = e (d.componentPairEndpointEquiv B (pr, 1)) := hab
    · exact hsecond

/-- The generic restricted-pair equivalence maps each component pair to the transported endpoint
pair or its swap. -/
theorem TwoPointDiagram.componentPairRestrictedEquiv_pair_eq_or_swap
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) {n : ℕ}
    (e : d.ComponentLeg B ≃ Fin (2 * n)) (localPairing : Pairing n)
    (hpartner : ∀ leg,
      localPairing.partner (e leg) =
        e (d.restrictedPartner (B : Finset (TwoPointVertex S)) leg))
    (pr : d.ComponentPair B) :
    (d.componentPairRestrictedEquiv B e localPairing hpartner pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 0)),
          e (d.componentPairEndpointEquiv B (pr, 1))) ∨
      (d.componentPairRestrictedEquiv B e localPairing hpartner pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 1)),
          e (d.componentPairEndpointEquiv B (pr, 0))) := by
  change
    (d.componentPairToRestricted B e localPairing pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 0)),
          e (d.componentPairEndpointEquiv B (pr, 1))) ∨
      (d.componentPairToRestricted B e localPairing pr).1 =
        (e (d.componentPairEndpointEquiv B (pr, 1)),
          e (d.componentPairEndpointEquiv B (pr, 0)))
  exact d.componentPairToRestricted_pair_eq_or_swap B e localPairing hpartner pr

/-- External-component pair restriction preserves transported endpoints up to swap. -/
theorem TwoPointDiagram.externalComponentPairEquiv_pair_eq_or_swap
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (pr : d.ComponentPair d.externalComponentPart) :
    (d.externalComponentPairEquiv pr).1 =
        (d.externalBlockLegEquiv
            (d.componentPairEndpointEquiv d.externalComponentPart (pr, 0)),
          d.externalBlockLegEquiv
            (d.componentPairEndpointEquiv d.externalComponentPart (pr, 1))) ∨
      (d.externalComponentPairEquiv pr).1 =
        (d.externalBlockLegEquiv
            (d.componentPairEndpointEquiv d.externalComponentPart (pr, 1)),
          d.externalBlockLegEquiv
            (d.componentPairEndpointEquiv d.externalComponentPart (pr, 0))) :=
  d.componentPairRestrictedEquiv_pair_eq_or_swap d.externalComponentPart
    d.externalBlockLegEquiv d.restrictedExternalPairing
    d.restrictedExternalPairing_partner_externalBlockLegEquiv pr

/-- Vacuum-component pair restriction preserves transported endpoints up to swap. -/
theorem TwoPointDiagram.vacuumComponentPairEquiv_pair_eq_or_swap
    {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B : d.componentPartition.parts) (hVac : d.ComponentIsVacuum B)
    (pr : d.ComponentPair B) :
    (d.vacuumComponentPairEquiv B hVac pr).1 =
        (d.vacuumBlockLegEquiv B hVac (d.componentPairEndpointEquiv B (pr, 0)),
          d.vacuumBlockLegEquiv B hVac (d.componentPairEndpointEquiv B (pr, 1))) ∨
      (d.vacuumComponentPairEquiv B hVac pr).1 =
        (d.vacuumBlockLegEquiv B hVac (d.componentPairEndpointEquiv B (pr, 1)),
          d.vacuumBlockLegEquiv B hVac (d.componentPairEndpointEquiv B (pr, 0))) :=
  d.componentPairRestrictedEquiv_pair_eq_or_swap B (d.vacuumBlockLegEquiv B hVac)
    (d.restrictedVacuumPairing B hVac)
    (d.restrictedVacuumPairing_partner_vacuumBlockLegEquiv B hVac) pr

end Common
end SecondQuantization
