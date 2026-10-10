import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedComponentPosition
import LeanCondensedMatter.Combinatorics.PerfectPairing.Transport

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

/-- Transporting a mixed-order partner back to the standard diagram enumeration recovers the
original generic diagram partner. -/
theorem TwoPointDiagram.mixedTimeAmbientPositionEquiv_partner
    {ExternalLabel : Type*} {InternalLabel : Type*} {n : ℕ}
    (d : TwoPointDiagram ExternalLabel InternalLabel n (Finset.univ : Finset (Fin n)))
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeAmbientPositionEquiv τ τ' σ
        ((d.pairingInMixedOrder τ τ' σ).partner p) =
      d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  change (mixedTimeAmbientPositionEquiv τ τ' σ)
      ((d.pairing.transport (mixedTimeAmbientPositionEquiv τ τ' σ)).partner p) =
    d.pairing.partner (mixedTimeAmbientPositionEquiv τ τ' σ p)
  simp

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
  have hpos :
      mixedTimeAmbientPositionEquiv τ τ' σ
          (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) =
        (twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm leg := by
    apply (twoPointLegEquiv (Finset.univ : Finset (Fin n))).injective
    rw [twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
      mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
      Equiv.apply_symm_apply]
  apply (mixedTimeOrderedAtomicLegEquiv τ τ' σ).injective
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    d.mixedTimeAmbientPositionEquiv_partner,
    hpos,
    TwoPointDiagram.atomicLegPartner]

end Common
end SecondQuantization
