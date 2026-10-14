import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumAmplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Core.SlotCongr

set_option linter.style.header false

/-!
# Canonical support coordinates for external/vacuum splitting

The support-side local mixed-to-fixed map should agree with the canonical
mixed-time permutation of a standalone external-insertion diagram indexed
by the increasing enumeration of the supported interaction slots.
-/

namespace SecondQuantization
namespace Fermionic

open Common

/-- In increasing support-slot coordinates, the external sector's mixed-to-fixed
position map is the inverse of the standard standalone mixed-time permutation. -/
theorem externalInsertionLeftMixedToFixedEquiv_eq_standardMixedPosition_symm
    {E n : ℕ} (T : Finset (Fin n))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    externalInsertionLeftMixedToFixedEquiv T externalTime σ =
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime
        (σ ∘ fun i : Fin T.card => (T.orderIsoOfFin rfl i).1)).symm := by
  apply Equiv.ext
  intro p
  simp [externalInsertionLeftMixedToFixedEquiv,
    externalInsertionStandardToMixedAtomicPositionEquiv,
    externalInsertionLegEquiv, externalInsertionInteractionLegEquiv]

end Fermionic
end SecondQuantization
