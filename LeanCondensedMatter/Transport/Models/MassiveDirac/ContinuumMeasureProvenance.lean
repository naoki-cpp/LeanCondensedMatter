import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac continuum measure provenance

This module is the model-local theorem seam relating the scalar prefactors that are intentionally
owned by different physical stages:

- `Transport.Core.ContinuumMeasure` owns the bare physical-momentum measure `d²p/(2πℏ)²`;
- the disorder measure owner binds one continuum Born disorder line to exactly one copy of that
  measure through `continuumBornDisorderMeasurePrefactor`;
- the Born self-energy owns the full-angle radial reduction `continuumBornAngularMeasurePrefactor`;
- `Conductivity.Normalization` owns the Bastin/Středa trace prefactor and the combined
  trace-plus-momentum-measure normalization.

The bridge equalities below make the placement of the angular `2π`, disorder line, continuum
measure, and trace normalization explicit without moving model-specific factors into generic
Transport. In particular, angular reduction and the shared disorder-measure stage compose to exactly
one physical momentum measure. Crossed real-space Fourier blocks already contain the momentum
measure upstream, so their eventual conductivity boundary must use the trace prefactor rather than
the combined normalization.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- The self-energy angular-reduced measure is one full-angle factor times the generic physical
momentum measure. -/
theorem continuumBornAngularMeasurePrefactor_eq_two_pi_mul_momentumMeasurePrefactor
    (hbar : ℝ) :
    continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * momentumMeasurePrefactor hbar := by
  rfl

/-- The shared continuum Born disorder-measure factor contains exactly one disorder line and one
unreduced physical-momentum measure. -/
theorem continuumBornDisorderMeasurePrefactor_eq_disorder_mul_momentumMeasure
    (disorderStrength hbar : ℝ) :
    continuumBornDisorderMeasurePrefactor disorderStrength hbar =
      disorderStrength * momentumMeasurePrefactor hbar := by
  rfl

/-- Attaching the disorder line to the self-energy angular-reduced measure is exactly one full-angle
`2π` multiplying the canonical disorder-measure stage. Thus the physical momentum measure occurs
exactly once. -/
theorem disorder_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_disorderMeasurePrefactor
    (disorderStrength hbar : ℝ) :
    disorderStrength * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * continuumBornDisorderMeasurePrefactor disorderStrength hbar := by
  unfold continuumBornAngularMeasurePrefactor continuumBornDisorderMeasurePrefactor
  ring

/-- For a radial response whose full polar angle has not yet been accounted for, restoring the
trace prefactor and angular-reduced measure is equivalent to one angular `2π` multiplying the
canonical non-crossing Bastin/Středa normalization. -/
theorem bastinTrace_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_normalization
    (hbar : ℝ) :
    bastinTraceConductivityPrefactor hbar * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * bastinStredaConductivityNormalization hbar := by
  unfold continuumBornAngularMeasurePrefactor bastinStredaConductivityNormalization
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
