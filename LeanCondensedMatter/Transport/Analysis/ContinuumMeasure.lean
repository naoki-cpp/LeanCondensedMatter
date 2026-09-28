import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Two-dimensional physical-momentum continuum measure

This module owns scalar normalizations for a two-dimensional continuum written in physical
momentum rather than wave vector:

```text
d²p / (2πℏ)².
```

The full-angle radial specialization also lives here now that multiple transport models consume it.
Both declarations are continuum-measure conventions, not model Hamiltonian, disorder, response, or
conductivity data.
-/

namespace QuantumTheory
namespace Transport

/-- The `ℏ`-dependent prefactor in the two-dimensional physical-momentum continuum measure
`d²p / (2πℏ)²`. This is a continuum convention rather than a generic transport invariant. -/
noncomputable def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

/-- The physical-momentum measure prefactor after an exact full-angle reduction,
`2π /(2πℏ)²`. The radial Jacobian `p` remains part of the radial integrand. -/
noncomputable def fullAngleMomentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  2 * Real.pi * momentumMeasurePrefactor hbar

end Transport
end QuantumTheory
