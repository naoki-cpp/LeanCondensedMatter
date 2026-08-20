import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Quartic leg families

Atomic time-evolved leg operators for a sequence of quartic vertex labels.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The atomic operator at a flattened leg position, for an arbitrary vertex-label sequence `q`
and time assignment `τ`**: look up which slot/local-leg the position corresponds to
(`Common.orderedQuarticLegEquiv`), and evolve that vertex's local-leg operator to the slot's assigned
time. -/
noncomputable def quarticLegOperatorForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  let slotLeg := Common.orderedQuarticLegEquiv n p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (q slotLeg.1) slotLeg.2)

end Fermionic
end SecondQuantization
