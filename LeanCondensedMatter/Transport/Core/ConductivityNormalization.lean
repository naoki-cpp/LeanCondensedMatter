import LeanCondensedMatter.Transport.Core.FiniteVolume
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-volume electric-field conductivity normalization

This module owns the representation-independent conversion from a total-current response to a
finite-volume electric-field conductivity. For the source convention

```text
A(t) ∝ exp (η t) exp (-i ω t),
```

the corresponding complex electric-field amplitude is

```text
E(t) = -∂ₜ A(t) = (-η + iω) A(t).
```

The conversion depends only on the positive physical volume and the driving/switching rates. It is
independent of Hilbert-space dimension, particle statistics, Hamiltonian, current realization, and
spectral representation. Concrete fermionic directional conductivities remain downstream.

No zero-switching, DC, infinite-volume, or gauge-equivalence limit is taken here.
-/

namespace QuantumTheory
namespace Transport

/-- For `A(t) ∝ exp (ηt) exp (-iωt)`, the electric-field amplitude is
`(-η + iω) A(t)`. -/
def adiabaticElectricFieldFactor (ω η : ℝ) : ℂ :=
  -(η : ℂ) + Complex.I * (ω : ℂ)

/-- Combined conversion from total-current/vector-potential response to
current-density/electric-field response. -/
noncomputable def finiteVolumeConductivityNormalization
    (volume : PositiveVolume) (ω η : ℝ) : ℂ :=
  (((volume.volume : ℂ) * adiabaticElectricFieldFactor ω η))⁻¹

/-- The finite-volume normalization denominator is nonzero whenever the driving frequency and
switching rate are not both zero. -/
theorem finiteVolumeConductivityDenominator_ne_zero
    (volume : PositiveVolume) (ω η : ℝ) (hrate : ω ≠ 0 ∨ η ≠ 0) :
    (volume.volume : ℂ) * adiabaticElectricFieldFactor ω η ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt volume.volume_pos
  · intro hzero
    have hre : -η = 0 := by
      simpa [adiabaticElectricFieldFactor] using congrArg Complex.re hzero
    have him : ω = 0 := by
      simpa [adiabaticElectricFieldFactor] using congrArg Complex.im hzero
    rcases hrate with hω | hη
    · exact hω him
    · exact hη (neg_eq_zero.mp hre)

/-- Convert a total-current response coefficient with respect to vector potential into an
intensive electric-field conductivity. -/
noncomputable def finiteVolumeConductivityFromVectorPotential
    (volume : PositiveVolume) (ω η : ℝ) (response : ℂ) : ℂ :=
  response * finiteVolumeConductivityNormalization volume ω η

end Transport
end QuantumTheory
