import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac continuum measure provenance

This module is the model-local theorem seam relating the scalar prefactors that are intentionally
owned by different physical stages:

- `Transport.Core.ContinuumMeasure` owns the bare physical-momentum measure `d²p/(2πℏ)²`;
- the Born self-energy owns the full-angle radial reduction `continuumBornAngularMeasurePrefactor`;
- the disorder measure owner supplies the external scalar-disorder-line factor
  `continuumBornRetardedAdvancedCurrentRungPrefactor` after a rung angular coefficient has already
  absorbed `2π`;
- `Conductivity.Normalization` owns the Bastin/Středa trace prefactor and the combined
  trace-plus-momentum-measure normalization.

The bridge equalities below make the placement of the angular `2π`, disorder line, continuum
measure, and trace normalization explicit without moving model-specific factors into generic
Transport. In particular, the self-energy and current-rung routes differ only in when the angular
factor is introduced, while both attach the physical momentum measure exactly once. Crossed
real-space Fourier blocks already contain the momentum measure upstream, so their eventual
conductivity boundary must use the trace prefactor rather than the combined normalization.
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

/-- The external retarded-advanced current-rung factor contains exactly one disorder line and one
unreduced physical-momentum measure. Its angular `2π` is already present in the rung coefficient. -/
theorem continuumBornRetardedAdvancedCurrentRungPrefactor_eq_disorder_mul_momentumMeasure
    (disorderStrength hbar : ℝ) :
    continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar =
      disorderStrength * momentumMeasurePrefactor hbar := by
  rfl

/-- The Born self-energy and retarded-advanced current-rung conventions differ only by the location
of the full-angle `2π` factor. Thus the disorder line and physical-momentum measure occur exactly
once in either route. -/
theorem disorder_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_currentRungPrefactor
    (disorderStrength hbar : ℝ) :
    disorderStrength * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) *
        continuumBornRetardedAdvancedCurrentRungPrefactor disorderStrength hbar := by
  unfold continuumBornAngularMeasurePrefactor
    continuumBornRetardedAdvancedCurrentRungPrefactor
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
