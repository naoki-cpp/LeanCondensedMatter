import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningCurrentVertex

set_option linter.style.header false

/-!
# Finite-broadening massive-Dirac ladder regularity

This module owns the common regularity condition for interpreting the algebraic finite-cutoff
finite-`η` Born-Dyson in-plane ladder coefficients as the actual solution of the two-component
fixed-point equation. The condition is independent of whether the solved vertex is consumed by a
longitudinal or Hall Středa response.

No conductivity normalization, response insertion, or disorder/broadening/ultraviolet limit is
introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Regularity condition under which the finite-cutoff Born-Dyson in-plane ladder coefficient pair
represents the actual fixed-point solution. -/
def finiteCutoffContinuumBornDysonLadderRegular
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : Prop :=
  inPlaneLadderDeterminant
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
        .x .x v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornDysonRetardedAdvancedCurrentRungCoefficient
        .y .x v m probeEnergy broadening disorderStrength hbar pMax) ≠ 0

/-- At zero disorder the finite-cutoff Born-Dyson ladder determinant is one. -/
@[simp]
theorem finiteCutoffContinuumBornDysonLadderRegular_zero_disorder
    (v m probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening 0 hbar pMax := by
  simp [finiteCutoffContinuumBornDysonLadderRegular, inPlaneLadderDeterminant]

end

end QuantumTheory.Transport.Models.MassiveDirac
