module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum

public section

set_option linter.style.header false

/-!
# Two-dimensional physical-momentum continuum measure

This module owns scalar normalizations for a two-dimensional continuum written in physical
momentum rather than wave vector:

```text
d²p / (2πℏ)².
```

The full-angle radial specialization also lives here now that multiple transport models consume it.
These declarations are continuum-measure conventions, not Euclidean kinematics, model Hamiltonian,
disorder, response, or conductivity data.
-/

namespace QuantumTheory
namespace Transport

/-- The `ℏ`-dependent prefactor in the two-dimensional physical-momentum continuum measure
`d²p / (2πℏ)²`. This is a continuum convention rather than a generic transport invariant. -/
@[expose] noncomputable def momentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  1 / (2 * Real.pi * hbar) ^ 2

/-- The physical-momentum measure prefactor after an exact full-angle reduction,
`2π /(2πℏ)²`. The radial Jacobian `p` remains part of the radial integrand. -/
@[expose] noncomputable def fullAngleMomentumMeasurePrefactor (hbar : ℝ) : ℝ :=
  2 * Real.pi * momentumMeasurePrefactor hbar

/-- The two-dimensional physical-momentum normalization is positive when ℏ is nonzero. -/
theorem momentumMeasurePrefactor_pos (hbar : ℝ) (hhbar : hbar ≠ 0) :
    0 < momentumMeasurePrefactor hbar := by
  unfold momentumMeasurePrefactor
  exact one_div_pos.mpr
    (sq_pos_of_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hhbar))

/-- Full-angle integration preserves positivity of the physical-momentum measure. -/
theorem fullAngleMomentumMeasurePrefactor_pos (hbar : ℝ) (hhbar : hbar ≠ 0) :
    0 < fullAngleMomentumMeasurePrefactor hbar := by
  unfold fullAngleMomentumMeasurePrefactor
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (momentumMeasurePrefactor_pos hbar hhbar)

end Transport
end QuantumTheory
