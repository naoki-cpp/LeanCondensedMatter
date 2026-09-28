import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Static Bastin–Středa conductivity normalization

This module owns scalar conductivity normalizations that depend only on the static
Bastin–Středa representation and the chosen continuum measure, not on a concrete Hamiltonian,
particle statistics, disorder model, or current realization.

Current vertices are assumed to carry their physical charge normalization already. A traced static
response therefore receives the standard trace prefactor `ℏ/(2π)`. Continuum measure normalization
is attached separately so response layers can make the measure provenance explicit and avoid
double-counting it.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Trace normalization for a static Bastin–Středa response before any continuum momentum measure
is attached. -/
def bastinStredaTraceConductivityPrefactor (hbar : ℝ) : ℝ :=
  hbar / (2 * Real.pi)

/-- Combined normalization for a static Bastin–Středa response with an explicitly supplied
continuum-measure normalization. -/
def bastinStredaConductivityNormalization
    (hbar measureNormalization : ℝ) : ℝ :=
  bastinStredaTraceConductivityPrefactor hbar * measureNormalization

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
