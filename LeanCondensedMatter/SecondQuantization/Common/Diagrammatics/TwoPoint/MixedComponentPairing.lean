import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedOrderPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentRestriction
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalSlotSplit

set_option linter.style.header false

/-!
# Mixed-time two-point pairing by full components

This module assigns mixed-time atomic positions of a generic two-point diagram to its connected
components. It transports component positions and restricted partners between mixed order and the
standard diagram-leg enumeration. The construction is independent of particle statistics, operator
algebra, and diagram amplitudes.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The full diagram component containing one mixed-time atomic position. -/
noncomputable def TwoPointDiagram.mixedPositionComponent
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    d.componentPartition.parts :=
  ⟨d.componentBlock
      (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p)),
    d.componentBlock_mem_componentPartition _⟩

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
  change d.componentBlock
      (twoPointVertexOfLeg
        (mixedTimeAmbientPositionEquiv τ τ' σ
          ((d.pairingInMixedOrder τ τ' σ).partner p))) =
    d.componentBlock
      (twoPointVertexOfLeg (mixedTimeAmbientPositionEquiv τ τ' σ p))
  rw [d.mixedTimeAmbientPositionEquiv_partner]
  exact d.componentBlock_vertexOfLeg_partner _

/-- Equality with a mixed-position component is exactly standard component-leg membership after
transport back from mixed time order. -/
theorem TwoPointDiagram.mixedPositionComponent_eq_iff_legInComponent
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * n + 1))) :
    d.mixedPositionComponent τ τ' σ p = B ↔
      d.legInComponent (B : Finset (TwoPointVertex
        (Finset.univ : Finset (Fin n))))
        (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- Mixed-time positions belonging to one full diagram component. -/
abbrev TwoPointDiagram.MixedComponentPosition
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :=
  {p : Fin (2 * (2 * n + 1)) // d.mixedPositionComponent τ τ' σ p = B}

/-- Positions of one mixed-time component are equivalent to the standard flattened legs of that
component. -/
noncomputable def TwoPointDiagram.mixedComponentPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :
    d.MixedComponentPosition τ τ' σ B ≃ d.ComponentLeg B :=
  (mixedTimeAmbientPositionEquiv τ τ' σ).subtypeEquiv fun p =>
    d.mixedPositionComponent_eq_iff_legInComponent τ τ' σ B p

/-- The mixed-order partner restricted to one full component-position fiber. -/
noncomputable def TwoPointDiagram.mixedRestrictedPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts) :
    Equiv.Perm (d.MixedComponentPosition τ τ' σ B) :=
  (d.pairingInMixedOrder τ τ' σ).partner.subtypePerm fun p => by
    rw [d.mixedPositionComponent_partner]

/-- The restricted mixed partner has the ambient mixed position as its underlying value. -/
theorem TwoPointDiagram.mixedRestrictedPartner_val
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (p : d.MixedComponentPosition τ τ' σ B) :
    (d.mixedRestrictedPartner τ τ' σ B p : Fin (2 * (2 * n + 1))) =
      (d.pairingInMixedOrder τ τ' σ).partner p :=
  congrArg Subtype.val (Equiv.Perm.subtypePerm_apply _ _ p)

/-- The mixed component-position equivalence intertwines the mixed restricted partner with the
standard component restricted partner. -/
@[simp]
theorem TwoPointDiagram.mixedComponentPositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
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

/-- Mixed positions in the external component, reindexed by the canonical left external split. -/
noncomputable def TwoPointDiagram.mixedExternalPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.MixedComponentPosition τ τ' σ d.externalComponentPart ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (d.externalComponent 0)).card + 1)) :=
  (d.mixedComponentPositionEquiv τ τ' σ d.externalComponentPart).trans
    d.externalComponentLegEquiv.symm

/-- Mixed positions in a vacuum component, reindexed as the legs of its restricted quartic
diagram. -/
noncomputable def TwoPointDiagram.mixedVacuumPositionEquiv
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B) :
    d.MixedComponentPosition τ τ' σ B ≃
      Fin (2 * (2 * (TwoPointDiagram.interactionPart
        (B : Finset (TwoPointVertex
          (Finset.univ : Finset (Fin n))))).card)) :=
  (d.mixedComponentPositionEquiv τ τ' σ B).trans
    (d.vacuumBlockLegEquiv B hVac)

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
    (τ τ' : ℝ) (σ : Fin n → ℝ) (B : d.componentPartition.parts)
    (hVac : d.ComponentIsVacuum B)
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
  rw [d.restrictedVacuumPairing_partner_vacuumBlockLegEquiv,
    d.mixedComponentPositionEquiv_partner]

end Common
end SecondQuantization
