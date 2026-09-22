import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.External.ExternalSlotSplit

set_option linter.style.header false

/-!
# Mixed-time pairing restricted by full components

`MixedComponentPosition` owns the statistics-independent component-position coordinates introduced by
#1206. This module adds only pairing-specific structure: preservation of component assignment by the
mixed-order partner and transport of restricted partners to the standard component-leg coordinates.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The mixed-order pairing partner remains in the same full component. -/
@[simp]
theorem TwoPointDiagram.mixedPositionComponent_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    d.mixedPositionComponent τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.mixedPositionComponent τ τ' σ p := by
  apply Subtype.ext
  change d.vertexGraph.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          ((d.pairingInMixedOrder τ τ' σ).partner p))) =
    d.vertexGraph.componentBlock
      (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
  rw [d.mixedTimeAmbientPositionEquiv_partner]
  exact d.vertexGraph.componentBlock_eq_of_reachable
    (d.pairing.vertexGraph_reachable_partner twoPointVertexOfLeg _)

/-- The mixed-order partner restricted to one full component-position fiber. -/
noncomputable def TwoPointDiagram.mixedRestrictedPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts) :
    Equiv.Perm (d.MixedComponentPosition τ τ' σ B) :=
  ((d.pairingInMixedOrder τ τ' σ).restrict
    (fun p => d.mixedPositionComponent τ τ' σ p = B)
    (fun p => by rw [d.mixedPositionComponent_partner])).partner

/-- The restricted mixed partner has the ambient mixed position as its underlying value. -/
theorem TwoPointDiagram.mixedRestrictedPartner_val
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    (d.mixedRestrictedPartner τ τ' σ B p : Fin (2 * (2 * n + 1))) =
      (d.pairingInMixedOrder τ τ' σ).partner p := by
  simpa only [TwoPointDiagram.mixedRestrictedPartner] using
    (d.pairingInMixedOrder τ τ' σ).restrict_partner_val
      (fun q => d.mixedPositionComponent τ τ' σ q = B)
      (fun q => by rw [d.mixedPositionComponent_partner]) p

/-- The mixed component-position equivalence intertwines the mixed restricted partner with the
standard component restricted partner. -/
@[simp]
private theorem TwoPointDiagram.mixedComponentPositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    d.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p) =
      d.restrictedPartner (B : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
        (d.mixedComponentPositionEquiv τ τ' σ B p) := by
  apply Subtype.ext
  change mixedTimeAmbientPositionEquiv τ τ' σ
      (d.mixedRestrictedPartner τ τ' σ B p) =
    (d.restrictedPartner (B : Finset (TwoPointVertex
      (Finset.univ : Finset (Fin n))))
      (d.mixedComponentPositionEquiv τ τ' σ B p) :
        Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)))
  rw [d.mixedRestrictedPartner_val, d.mixedTimeAmbientPositionEquiv_partner,
    d.restrictedPartner_val]
  apply congrArg d.pairing.partner
  rfl

/-- The canonical external split pairing partner is the transport of the mixed restricted partner. -/
theorem TwoPointDiagram.externalVacuumSplit_fst_partner_mixedExternalPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (p : d.MixedComponentPosition τ τ' σ d.externalComponentPart) :
    d.externalVacuumSplit.1.pairing.partner
        (d.mixedExternalPositionEquiv τ τ' σ p) =
      d.mixedExternalPositionEquiv τ τ' σ
        (d.mixedRestrictedPartner τ τ' σ d.externalComponentPart p) := by
  change d.externalVacuumSplit.1.pairing.partner
      (d.externalComponentLegEquiv.symm
        (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart p)) =
    d.externalComponentLegEquiv.symm
      (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart
        (d.mixedRestrictedPartner τ τ' σ d.externalComponentPart p))
  rw [← d.externalComponentLegEquiv_symm_restrictedPartner,
    d.mixedComponentPositionEquiv_partner]

/-- A vacuum restricted pairing partner is the transport of the corresponding mixed restricted
partner. -/
theorem TwoPointDiagram.restrictedVacuumPairing_partner_mixedVacuumPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.vertexGraph.componentPartition.parts)
    (hVac : ComponentIsVacuum (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin n)))))
    (p : d.MixedComponentPosition τ τ' σ B) :
    (d.restrictedVacuumPairing B hVac).partner
        (d.mixedVacuumPositionEquiv τ τ' σ B hVac p) =
      d.mixedVacuumPositionEquiv τ τ' σ B hVac
        (d.mixedRestrictedPartner τ τ' σ B p) := by
  change (d.restrictedVacuumPairing B hVac).partner
      (d.vacuumBlockLegEquiv B hVac
        (d.mixedComponentPositionEquiv τ τ' σ B p)) =
    d.vacuumBlockLegEquiv B hVac
      (d.mixedComponentPositionEquiv τ τ' σ B
        (d.mixedRestrictedPartner τ τ' σ B p))
  rw [d.mixedComponentPositionEquiv_partner]
  simpa only [TwoPointDiagram.restrictedVacuumPairing, TwoPointDiagram.restrictedPartner] using
    d.pairing.restrictAlongEquiv_partner (d.legInComponent B)
      (fun i => d.legInComponent_partner_iff B i) (d.vacuumBlockLegEquiv B hVac)
      (d.mixedComponentPositionEquiv τ τ' σ B p)

end Common
end SecondQuantization
