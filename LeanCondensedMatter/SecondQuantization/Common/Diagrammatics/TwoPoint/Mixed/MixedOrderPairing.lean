import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.ExternalInsertionBridge
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.MixedOrder

set_option linter.style.header false

/-!
# Mixed-order pairing for generic two-point diagrams

This module owns the statistics-independent transport of a two-point diagram pairing from the
standard external-plus-interaction leg enumeration to the mixed imaginary-time atomic enumeration.
The mixed-position coordinate transport and its pairing compatibility are packaged together.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/-- The standard diagram-leg position underlying a mixed-time atomic position. -/
noncomputable def mixedTimeAmbientPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Fin (2 * (2 * n + 1)) ≃
      Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1)) :=
  (standardToMixedAtomicPositionEquiv τ τ' σ).symm.trans (finCongr (by simp))

/-- Unflattening the standard ambient position underlying a mixed position recovers the atomic leg
identity stored at that mixed position. -/
theorem twoPointLegEquiv_mixedTimeAmbientPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p := by
  unfold mixedTimeAmbientPositionEquiv standardToMixedAtomicPositionEquiv
  rw [← (twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply
    (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)]
  apply congrArg (twoPointLegEquiv (Finset.univ : Finset (Fin n)))
  apply Fin.ext
  rfl

/-- Returning the mixed-time position of an atomic leg to the standard flattened
coordinate recovers its fixed two-point leg position. -/
theorem mixedTimeAmbientPositionEquiv_mixedTimeOrderedAtomicLegPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    mixedTimeAmbientPositionEquiv τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) =
      (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm leg := by
  apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
  rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    Equiv.apply_symm_apply]

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
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    mixedTimeOrderedAtomicLegEquiv_eq_externalInsertion]
  exact externalInsertionLegEquiv_mixedTimeAmbientPositionEquiv
    (E := 1) (n := n) (twoPointExternalTimes τ τ') σ p

end Common
end SecondQuantization
