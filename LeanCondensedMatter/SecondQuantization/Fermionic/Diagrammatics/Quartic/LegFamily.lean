import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Fermionic quartic leg families

This module owns the diagram-independent fermionic semantics of a flattened sequence of quartic
vertex legs: time-labelled fields, evolved operators, and their free-evolution energy shifts.

Dyson and Wick diagrammatics consume these declarations directly.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The time-labelled fermionic field at a flattened leg position for an arbitrary vertex-label
sequence and time assignment. -/
noncomputable def quarticLegFieldForSequence {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    TimedField Mode :=
  let slotLeg := Common.orderedQuarticLegEquiv n p
  ⟨τ slotLeg.1, quarticLocalLegExternalFieldLabel (q slotLeg.1) slotLeg.2⟩

/-- The atomic operator at a flattened leg position for an arbitrary vertex-label sequence and time
assignment. -/
noncomputable def quarticLegOperatorForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  let slotLeg := Common.orderedQuarticLegEquiv n p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (q slotLeg.1) slotLeg.2)

omit [Fintype Mode] in
/-- Mapping the canonical quartic leg field to its operator recovers the operator family. -/
theorem timedFieldOperator_quarticLegFieldForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    timedFieldOperator ε (quarticLegFieldForSequence q τ p) =
      quarticLegOperatorForSequence ε q τ p := by
  rw [quarticLegFieldForSequence, quarticLegOperatorForSequence, timedFieldOperator_quarticLocalLeg]

omit [Fintype Mode] in
/-- The free-evolution energy shift of a flattened quartic leg in an arbitrary vertex-label
sequence. -/
noncomputable def quarticLegEnergyShiftForSequence {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (p : Fin (2 * (2 * n))) : ℝ :=
  quarticLocalLegEnergyShift ε (q (flatVertexIndex n p)) (flatLocalLeg n p)

omit [Fintype Mode] in
/-- Every flattened quartic leg operator is its bare local-leg operator multiplied by the expected
imaginary-time exponential. -/
theorem quarticLegOperatorForSequence_eq_smul {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    quarticLegOperatorForSequence ε q τ p =
      Complex.exp ((τ (flatVertexIndex n p) *
        quarticLegEnergyShiftForSequence ε q p : ℝ) : ℂ) •
        quarticLocalLegOperator (q (flatVertexIndex n p)) (flatLocalLeg n p) := by
  rw [quarticLegOperatorForSequence, imaginaryTimeEvolve_quarticLocalLegOperator]
  rfl

end Fermionic
end SecondQuantization
