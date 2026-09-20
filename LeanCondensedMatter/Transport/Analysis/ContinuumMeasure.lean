import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.style.header false

/-!
# Two-dimensional physical-momentum continuum measure

This module owns the scalar normalization for a two-dimensional continuum written in physical
momentum rather than wave vector:

```text
d²p / (2πℏ)².
```

This is an explicit two-dimensional continuum convention, not a dimension-independent transport
invariant. Consumers that use physical-momentum continuum integrals should import this owner
directly. Angular or radial reductions remain with the layers that actually perform those
reductions until a shared reduced-measure API has a concrete cross-model consumer.

No model Hamiltonian, disorder approximation, response kernel, or conductivity normalization is
introduced here.
-/

namespace QuantumTheory
namespace Transport

/-- The `ℏ`-dependent prefactor in the two-dimensional physical-momentum continuum measure
`d²p / (2πℏ)²`. This is a continuum convention rather than a generic transport invariant. -/
noncomputable def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

end Transport
end QuantumTheory
