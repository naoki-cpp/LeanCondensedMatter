import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Continuum physical-momentum measure normalization

This module owns the representation-independent scalar normalization for a two-dimensional
continuum written in physical momentum rather than wave vector. The full Cartesian measure is

```text
d²p / (2πℏ)²,
```

and after a full polar-angle integration the remaining radial `p dp` integral carries one
additional factor of `2π`.

No model Hamiltonian, disorder approximation, response kernel, or conductivity normalization is
introduced here.
-/

namespace QuantumTheory
namespace Transport

/-- The `ℏ`-dependent prefactor in the two-dimensional physical-momentum continuum measure
`d²p / (2πℏ)²`. -/
def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

/-- The physical-momentum prefactor after integrating a full polar angle, so the remaining measure
is `radialMomentumMeasurePrefactor ℏ * p dp`. -/
def radialMomentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  2 * Real.pi * momentumMeasurePrefactor hbar

end Transport
end QuantumTheory
