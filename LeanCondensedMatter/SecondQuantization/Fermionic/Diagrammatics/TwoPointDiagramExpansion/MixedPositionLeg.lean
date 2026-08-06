import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedEventBlockOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairing

set_option linter.style.header false

/-!
# Standard leg identities underlying mixed atomic positions

The mixed-time atomic enumeration and the standard two-point diagram enumeration are related by the
permutation constructed in `Reindexing.lean`.  This module records the pointwise coordinate identity
needed by the event-block crossing argument.
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

end Fermionic
end SecondQuantization
