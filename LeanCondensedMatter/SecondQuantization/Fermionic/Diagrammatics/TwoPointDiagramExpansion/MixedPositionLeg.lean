import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.MixedComponentPosition
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairing

set_option linter.style.header false

/-!
# Pairing identities underlying mixed atomic positions

Common owns the standard-leg identity and inverse-coordinate facts for mixed atomic positions. This
module retains the pairing-specific fixed-external consequences: the diagram pairing as a map on leg
identities and its relation to the mixed-order partner permutation.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*}

/-- **The diagram pairing as a map on leg identities.** No enumeration of the legs is involved, so
this carries no reference to the times. -/
noncomputable def FixedExternalTwoPointWickDiagram.atomicLegPartner {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j) (leg : OrderedTwoPointLeg n) :
    OrderedTwoPointLeg n :=
  Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
    (d.1.pairing.partner
      ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm leg))

/-- **The mixed-order partner is the leg partner, conjugated by the mixed enumeration.** Reading the
leg identity at a mixed position, pairing it, and selecting the position of the partner leg is the
mixed-order partner permutation. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_partner_eq_atomicLegPartner
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    (d.pairingInMixedOrder τ τ' σ).partner p =
      mixedTimeOrderedAtomicLegPosition τ τ' σ
        (d.atomicLegPartner (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)) := by
  apply (mixedTimeOrderedAtomicLegEquiv τ τ' σ).injective
  rw [mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    ← twoPointLegEquiv_mixedTimeAmbientPositionEquiv,
    d.mixedTimeAmbientPositionEquiv_partner]
  rw [FixedExternalTwoPointWickDiagram.atomicLegPartner,
    (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm_apply_apply]

/-- The mixed-order partner of the position selected by a leg identity is the position selected by
the partner leg. -/
theorem FixedExternalTwoPointWickDiagram.pairingInMixedOrder_partner_legPosition
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    (d.pairingInMixedOrder τ τ' σ).partner
        (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) =
      mixedTimeOrderedAtomicLegPosition τ τ' σ (d.atomicLegPartner leg) := by
  rw [d.pairingInMixedOrder_partner_eq_atomicLegPartner,
    mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition]

end Fermionic
end SecondQuantization
