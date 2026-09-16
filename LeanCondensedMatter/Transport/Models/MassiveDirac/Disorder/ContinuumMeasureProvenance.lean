import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy

set_option linter.style.header false

/-!
# Massive-Dirac continuum-disorder measure provenance

This module is the shared scalar provenance seam between the continuum Born self-energy and
retarded-advanced current-rung routes. The generic physical-momentum measure remains owned by
`Transport.Core.ContinuumMeasure`.

The Born self-energy performs its full polar-angle reduction before the external scalar-disorder
factor is attached, so its radial formula uses `disorderStrength * continuumBornAngularMeasurePrefactor
hbar`. The retarded-advanced current-rung angular coefficients already contain their full `2π`
angle integral, so the external rung factor contains only one disorder line and the unreduced
physical-momentum measure. The bridge theorem below records that these two conventions differ by
exactly one angular `2π` and therefore attach the momentum measure exactly once.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- External scalar-disorder line together with one physical-momentum continuum measure factor.

Use this after an angular kernel has already been integrated over the full polar angle. -/
def continuumBornRetardedAdvancedCurrentRungPrefactor
    (disorderStrength hbar : ℝ) : ℝ :=
  disorderStrength * momentumMeasurePrefactor hbar

/-- The Born self-energy angular-reduced measure is exactly one full-angle factor times the generic
physical-momentum measure. -/
theorem continuumBornAngularMeasurePrefactor_eq_two_pi_mul_momentumMeasurePrefactor
    (hbar : ℝ) :
    continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * momentumMeasurePrefactor hbar := by
  rfl

/-- The self-energy and current-rung continuum conventions differ only by where the full-angle
`2π` factor is introduced. In particular, the external disorder line and physical-momentum measure
are attached exactly once in either route. -/
theorem disorder_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_currentRungPrefactor
    (disorderStrength hbar : ℝ) :
    disorderStrength * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) *
        continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar := by
  unfold continuumBornAngularMeasurePrefactor
    continuumBornRetardedAdvancedCurrentRungPrefactor
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
