import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Continuum physical-momentum measure normalization

This module owns the representation-independent scalar normalization for a two-dimensional
continuum written in physical momentum rather than wave vector:

```text
d²p / (2πℏ)².
```

Angular or radial reductions remain with the layers that actually perform those reductions until a
shared reduced-measure API has a concrete cross-model consumer.

No model Hamiltonian, disorder approximation, response kernel, or conductivity normalization is
introduced here.
-/

namespace QuantumTheory
namespace Transport

/-- The `ℏ`-dependent prefactor in the two-dimensional physical-momentum continuum measure
`d²p / (2πℏ)²`. -/
def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

end Transport
end QuantumTheory
