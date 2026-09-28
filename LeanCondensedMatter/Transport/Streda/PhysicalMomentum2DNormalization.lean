import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional physical-momentum Bastin–Středa normalization

This opt-in module specializes the dimension-independent static Bastin–Středa trace normalization
to the two-dimensional physical-momentum convention `d²p/(2πℏ)²` owned by
`Transport.Analysis.ContinuumMeasure`. Keeping this specialization outside the generic
`Transport.Streda` umbrella prevents a two-dimensional continuum convention from becoming an
implicit dependency of dimension-independent Středa response theory.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Static Bastin–Středa normalization specialized to the canonical two-dimensional
physical-momentum measure `d²p/(2πℏ)²`. -/
def bastinStredaPhysicalMomentumConductivityNormalization (hbar : ℝ) : ℝ :=
  bastinStredaConductivityNormalization hbar (momentumMeasurePrefactor hbar)

/-- Attaching the trace prefactor to the exact full-angle radial measure is one angular `2π`
times the canonical two-dimensional physical-momentum conductivity normalization. -/
theorem bastinStredaTrace_mul_fullAngleMomentumMeasurePrefactor_eq
    (hbar : ℝ) :
    bastinStredaTraceConductivityPrefactor hbar * fullAngleMomentumMeasurePrefactor hbar =
      (2 * Real.pi) * bastinStredaPhysicalMomentumConductivityNormalization hbar := by
  unfold fullAngleMomentumMeasurePrefactor bastinStredaPhysicalMomentumConductivityNormalization
    bastinStredaConductivityNormalization
  ring

end

end Transport
end QuantumTheory
