import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Positive physical volume and finite-volume conductivity normalization

This module owns the positive finite physical volume datum and the representation-independent
conversion from a total-current response to a finite-volume electric-field conductivity.
For the source convention

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

/-- A positive finite physical volume, independent of the response or model carrying it. -/
structure PositiveVolume where
  /-- Physical volume of the finite sample. -/
  volume : ℝ
  volume_pos : 0 < volume

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

/-- At zero frequency, the electric-field normalization keeps the finite switching rate and volume
explicit. -/
theorem finiteVolumeConductivityNormalization_zero_frequency
    (convention : PositiveVolume) (eta : ℝ) :
    finiteVolumeConductivityNormalization convention 0 eta =
      (((convention.volume : ℂ) * (-(eta : ℂ))))⁻¹ := by
  simp [finiteVolumeConductivityNormalization, adiabaticElectricFieldFactor]

end Transport
end QuantumTheory
