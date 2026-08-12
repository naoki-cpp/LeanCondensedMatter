import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedEventBlockOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairing

set_option linter.style.header false

/-!
# Standard leg identities underlying mixed atomic positions

The mixed-time atomic enumeration and the standard two-point diagram enumeration are related by the
permutation constructed in `Reindexing.lean`.  This module records the pointwise coordinate identity
needed by the event-block crossing argument.

It also reads the pairing off at the level of leg identities.  The mixed-order partner permutation
depends on the times only through the enumeration, so conjugating it back to leg identities leaves a
map on `OrderedTwoPointLeg n` in which no time appears.  That is the form in which the pairing can be
compared with the pairing of a sub-diagram, which lives on a different slot count and therefore
carries different times.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Unflattening the standard ambient position underlying a mixed position recovers the atomic leg
identity stored at that mixed position. -/
theorem twoPointLegEquiv_mixedTimeAmbientPositionEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))
        (mixedTimeAmbientPositionEquiv τ τ' σ p) =
      mixedTimeOrderedAtomicLegEquiv τ τ' σ p := by
  unfold mixedTimeAmbientPositionEquiv standardToMixedAtomicPositionEquiv
  rw [← (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).apply_symm_apply
    (mixedTimeOrderedAtomicLegEquiv τ τ' σ p)]
  apply congrArg (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)))
  apply Fin.ext
  rfl

/-- The position selected by an atomic leg identity is inverse to reading the identity at a mixed
position. -/
@[simp]
theorem mixedTimeOrderedAtomicLegPosition_mixedTimeOrderedAtomicLegEquiv {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    mixedTimeOrderedAtomicLegPosition τ τ' σ
        (mixedTimeOrderedAtomicLegEquiv τ τ' σ p) = p := by
  exact (mixedTimeOrderedAtomicLegEquiv τ τ' σ).symm_apply_apply p

/-- Reading the atomic identity at the position selected by that identity is identity. -/
@[simp]
theorem mixedTimeOrderedAtomicLegEquiv_mixedTimeOrderedAtomicLegPosition {n : ℕ}
    (τ τ' : ℝ) (σ : Fin n → ℝ) (leg : OrderedTwoPointLeg n) :
    mixedTimeOrderedAtomicLegEquiv τ τ' σ
        (mixedTimeOrderedAtomicLegPosition τ τ' σ leg) = leg := by
  exact (mixedTimeOrderedAtomicLegEquiv τ τ' σ).apply_symm_apply leg

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
