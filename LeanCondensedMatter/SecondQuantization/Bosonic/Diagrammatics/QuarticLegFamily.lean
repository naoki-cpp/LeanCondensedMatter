import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Leg
import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.QuarticLocalLeg

set_option linter.style.header false

/-!
# Bosonic quartic leg families

Atomic time-evolved bosonic leg operators for a sequence of quartic vertex labels.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- The time-evolved bosonic operator at a flattened quartic-leg position. -/
noncomputable def quarticLegOperatorForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  let slotLeg := orderedQuarticLegEquiv n p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (q slotLeg.1) slotLeg.2)

end Bosonic
end SecondQuantization
