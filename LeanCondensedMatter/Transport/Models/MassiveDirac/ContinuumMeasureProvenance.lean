import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.Born.SelfEnergy
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.ContinuumMeasurePrefactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization

set_option linter.style.header false

/-!
# Massive-Dirac continuum measure provenance

This module records only cross-owner equalities between the continuum Born disorder/measure stage,
self-energy angular reduction, and Bastin/Středa conductivity normalization. Bare definitional
expansions remain with their owning definitions rather than receiving parallel public theorem names.

Crossed real-space Fourier blocks already contain the momentum measure upstream, so their eventual
conductivity boundary must use the trace-only prefactor rather than the combined normalization.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Attaching the disorder line to the self-energy angular-reduced measure is exactly one full-angle
`2π` multiplying the canonical disorder-measure stage. -/
theorem disorder_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_disorderMeasurePrefactor
    (disorderStrength hbar : ℝ) :
    disorderStrength * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * continuumBornDisorderMeasurePrefactor disorderStrength hbar := by
  unfold continuumBornAngularMeasurePrefactor continuumBornDisorderMeasurePrefactor
  ring

/-- For a radial response whose full polar angle has not yet been accounted for, restoring the trace
prefactor and angular-reduced measure is one angular `2π` times the canonical combined normalization. -/
theorem bastinTrace_mul_continuumBornAngularMeasurePrefactor_eq_two_pi_mul_normalization
    (hbar : ℝ) :
    bastinTraceConductivityPrefactor hbar * continuumBornAngularMeasurePrefactor hbar =
      (2 * Real.pi) * bastinStredaConductivityNormalization hbar := by
  unfold continuumBornAngularMeasurePrefactor bastinStredaConductivityNormalization
  ring

end

end QuantumTheory.Transport.Models.MassiveDirac
