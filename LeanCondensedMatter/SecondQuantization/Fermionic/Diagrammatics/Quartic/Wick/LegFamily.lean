import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Quartic leg families

Time-labelled fields and their atomic time-evolved operators for a sequence of quartic vertex labels.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The time-labelled fermionic field at a flattened leg position for an arbitrary vertex-label
sequence and time assignment. -/
noncomputable def quarticLegFieldForSequence {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    TimedField Mode :=
  let slotLeg := Common.orderedQuarticLegEquiv n p
  ⟨τ slotLeg.1, quarticLocalLegExternalFieldLabel (q slotLeg.1) slotLeg.2⟩

/-- **The atomic operator at a flattened leg position, for an arbitrary vertex-label sequence `q`
and time assignment `τ`**: look up which slot/local-leg the position corresponds to
(`Common.orderedQuarticLegEquiv`), and evolve that vertex's local-leg operator to the slot's assigned
time. -/
noncomputable def quarticLegOperatorForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  let slotLeg := Common.orderedQuarticLegEquiv n p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (q slotLeg.1) slotLeg.2)

omit [Fintype Mode] in
/-- Mapping the canonical quartic leg field to its operator recovers the existing operator family. -/
theorem timedFieldOperator_quarticLegFieldForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    timedFieldOperator ε (quarticLegFieldForSequence q τ p) =
      quarticLegOperatorForSequence ε q τ p := by
  rw [quarticLegFieldForSequence, quarticLegOperatorForSequence, timedFieldOperator_quarticLocalLeg]

end Fermionic
end SecondQuantization
