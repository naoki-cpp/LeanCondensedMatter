import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.ExternalInsertionBridge
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder

set_option linter.style.header false

/-!
# Mixed-order pairing for generic two-point diagrams

This module owns the statistics-independent transport of a two-point diagram pairing from the
standard external-plus-interaction leg enumeration to the mixed imaginary-time atomic enumeration.
The mixed-position coordinate system itself is owned by `MixedComponentPosition`.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- A generic two-point diagram pairing transported into mixed-time atomic order. -/
noncomputable def TwoPointDiagram.pairingInMixedOrder
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (2 * n + 1) :=
  d.pairing.transport (mixedTimeAmbientPositionEquiv τ τ' σ)

/-- The diagram pairing as a map on atomic leg identities; this map is independent of the mixed-time
enumeration. -/
noncomputable def TwoPointDiagram.atomicLegPartner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (leg : OrderedTwoPointLeg n) : OrderedTwoPointLeg n :=
  twoPointLegEquiv (Finset.univ : Finset (Fin n))
    (d.pairing.partner
      ((twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm leg))

/-- The mixed-order partner of the position selected by a leg identity is the position selected by
the partner leg. -/
theorem TwoPointDiagram.pairingInMixedOrder_partner_legPosition
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    (d.pairingInMixedOrder τ τ' σ).partner
        (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) =
      mixedTimeOrderedAtomicLegPosition τ τ' σ (d.atomicLegPartner leg) := by
  apply (mixedTimeOrderedAtomicLegEquiv τ τ' σ).injective
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    TwoPointDiagram.pairingInMixedOrder, PairingOn.transport_partner,
    Equiv.apply_symm_apply,
    mixedTimeAmbientPositionEquiv_mixedTimeOrderedAtomicLegPosition,
    TwoPointDiagram.atomicLegPartner]

/-- Transport through the fixed-leg coordinate bridge leaves the actual
mixed-time pairing unchanged, not merely its unoriented edges. -/
theorem twoPointDiagramExternalInsertionEquiv_pairingInMixedOrder
    {ExternalLabel InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    (twoPointDiagramExternalInsertionEquiv Finset.univ d).pairingInMixedOrder
        (twoPointExternalTimes τ τ') σ =
      d.pairingInMixedOrder τ τ' σ := by
  change (d.pairing.transport (twoPointExternalInsertionLegEquiv Finset.univ).symm).transport
      (externalInsertionMixedTimeAmbientPositionEquiv (twoPointExternalTimes τ τ') σ) =
    d.pairing.transport (mixedTimeAmbientPositionEquiv τ τ' σ)
  rw [PairingOn.transport_trans]
  congr 1
  apply Equiv.ext
  intro p
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  simp only [Equiv.trans_apply, twoPointExternalInsertionLegEquiv,
    Equiv.symm_trans_apply, Equiv.apply_symm_apply,
    externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_eq_externalInsertion]

end Common
end SecondQuantization
