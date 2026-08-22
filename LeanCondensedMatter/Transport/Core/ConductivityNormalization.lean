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

@[simp]
theorem adiabaticElectricFieldFactor_re (ω η : ℝ) :
    (adiabaticElectricFieldFactor ω η).re = -η := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_im (ω η : ℝ) :
    (adiabaticElectricFieldFactor ω η).im = ω := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_zero_frequency (η : ℝ) :
    adiabaticElectricFieldFactor 0 η = -(η : ℂ) := by
  simp [adiabaticElectricFieldFactor]

@[simp]
theorem adiabaticElectricFieldFactor_zero_switching (ω : ℝ) :
    adiabaticElectricFieldFactor ω 0 = Complex.I * (ω : ℂ) := by
  simp [adiabaticElectricFieldFactor]

/-- A strictly positive switching rate keeps the electric-field conversion factor nonzero, even at
zero driving frequency. -/
theorem adiabaticElectricFieldFactor_ne_zero_of_pos
    (ω η : ℝ) (hη : 0 < η) :
    adiabaticElectricFieldFactor ω η ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [adiabaticElectricFieldFactor] at hre
  linarith

/-- Combined conversion from total-current/vector-potential response to
current-density/electric-field response. -/
noncomputable def finiteVolumeConductivityNormalization
    (volume : PositiveVolume) (ω η : ℝ) : ℂ :=
  (((volume.volume : ℂ) * adiabaticElectricFieldFactor ω η))⁻¹

/-- The finite-volume normalization denominator is nonzero at every positive switching rate. -/
theorem finiteVolumeConductivityDenominator_ne_zero
    (volume : PositiveVolume) (ω η : ℝ) (hη : 0 < η) :
    (volume.volume : ℂ) * adiabaticElectricFieldFactor ω η ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt volume.volume_pos
  · exact adiabaticElectricFieldFactor_ne_zero_of_pos ω η hη

/-- Convert a total-current response coefficient with respect to vector potential into an
intensive electric-field conductivity. -/
noncomputable def finiteVolumeConductivityFromVectorPotential
    (volume : PositiveVolume) (ω η : ℝ) (response : ℂ) : ℂ :=
  response * finiteVolumeConductivityNormalization volume ω η

end Transport
end QuantumTheory
