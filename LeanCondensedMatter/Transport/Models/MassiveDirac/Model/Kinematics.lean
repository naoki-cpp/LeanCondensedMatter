import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial kinematics of the two-dimensional massive Dirac model

This file owns radial dispersion facts shared by longitudinal response and the Bastin radial-energy
bridge.  These facts depend only on the clean massive-Dirac spectrum; occupation and transport
relaxation enter downstream.

For

```text
E(p) = sqrt(v^2 p^2 + m^2),
```

the radial derivative away from a zero-energy degeneracy is

```text
dE/dp = v^2 p / E(p).
```

For an isotropic Fermi circle, projecting the radial group velocity onto the `x` axis gives a
`cos θ` factor.  Its full-angle mean square is derived below rather than inserted as an unexplained
factor of `1/2`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- The positive Dirac energy is nonnegative for every momentum. -/
theorem energy_nonneg (v m px py : ℝ) :
    0 ≤ energy v m px py := by
  exact Real.sqrt_nonneg _

/-- The massive-Dirac energy is bounded below by the mass magnitude uniformly in momentum. -/
theorem abs_mass_le_energy (v m px py : ℝ) :
    |m| ≤ energy v m px py := by
  have hkin : 0 ≤ v ^ 2 * (px ^ 2 + py ^ 2) := by
    positivity
  have hsq : |m| ^ 2 ≤ energy v m px py ^ 2 := by
    rw [energy_sq]
    unfold energySq
    rw [sq_abs]
    linarith
  have hm : 0 ≤ |m| := abs_nonneg m
  have hE := energy_nonneg v m px py
  nlinarith

/-- Any nonzero Dirac mass keeps the model uniformly away from the Dirac degeneracy. -/
theorem energy_pos_of_mass_ne_zero (v m px py : ℝ) (hm : m ≠ 0) :
    0 < energy v m px py := by
  have hmSq : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hsq : 0 < energy v m px py ^ 2 := by
    rw [energy_sq]
    unfold energySq
    have hkin : 0 ≤ v ^ 2 * (px ^ 2 + py ^ 2) := by positivity
    linarith
  have hE := energy_nonneg v m px py
  nlinarith

/-- The massive-Dirac dispersion polynomial is radial in polar momentum coordinates. -/
@[simp] theorem energySq_polar (v m p θ : ℝ) :
    energySq v m (p * Real.cos θ) (p * Real.sin θ) = energySq v m p 0 := by
  unfold energySq
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq θ
  calc
    v ^ 2 * ((p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2) + m ^ 2 =
        v ^ 2 * p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) + m ^ 2 := by ring
    _ = v ^ 2 * p ^ 2 + m ^ 2 := by rw [htrig]; ring
    _ = v ^ 2 * (p ^ 2 + 0 ^ 2) + m ^ 2 := by ring

/-- The positive massive-Dirac energy is radial in polar momentum coordinates. -/
@[simp] theorem energy_polar_eq_radial (v m p θ : ℝ) :
    energy v m (p * Real.cos θ) (p * Real.sin θ) = energy v m p 0 := by
  unfold energy
  rw [energySq_polar]

/-- Radial derivative of the positive massive-Dirac energy. -/
def radialEnergyDerivative (v m p : ℝ) : ℝ :=
  v ^ 2 * p / energy v m p 0

/-- The positive radial massive-Dirac dispersion has derivative `v² p / E` for nonzero mass. -/
theorem hasDerivAt_energy_radial
    (v m p : ℝ) (hm : m ≠ 0) :
    HasDerivAt (fun q : ℝ => energy v m q 0) (radialEnergyDerivative v m p) p := by
  have hpow : HasDerivAt (fun q : ℝ => q ^ 2) (2 * p) p := by
    simpa using (hasDerivAt_pow 2 p)
  have hmul :
      HasDerivAt (fun q : ℝ => v ^ 2 * q ^ 2) (v ^ 2 * (2 * p)) p := by
    exact HasDerivAt.const_mul (v ^ 2) hpow
  have hpoly :
      HasDerivAt (fun q : ℝ => energySq v m q 0) (v ^ 2 * (2 * p)) p := by
    simpa [energySq] using hmul.add_const (m ^ 2)
  have hmSq : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hsq_ne : energySq v m p 0 ≠ 0 := by
    unfold energySq
    positivity
  have hsqrt := hpoly.sqrt hsq_ne
  unfold radialEnergyDerivative energy
  convert hsqrt using 1
  field_simp [ne_of_gt (energy_pos_of_mass_ne_zero v m p 0 hm)]

/-- The radial energy derivative is continuous for nonzero mass. -/
theorem continuous_radialEnergyDerivative
    (v m : ℝ) (hm : m ≠ 0) :
    Continuous (radialEnergyDerivative v m) := by
  unfold radialEnergyDerivative
  have hE : Continuous (fun p : ℝ => energy v m p 0) := by
    unfold energy energySq
    fun_prop
  exact (continuous_const.mul continuous_id).div hE
    (fun p => ne_of_gt (energy_pos_of_mass_ne_zero v m p 0 hm))

/-- `x` component obtained by projecting the radial group velocity onto polar angle `θ`. -/
def radialGroupVelocityX (v m p θ : ℝ) : ℝ :=
  radialEnergyDerivative v m p * Real.cos θ

/-- Full-angle mean square of the `x` component of the radial group velocity. -/
def isotropicMeanSquareRadialGroupVelocityX (v m p : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), radialGroupVelocityX v m p θ ^ 2) /
    (2 * Real.pi)

/-- In two dimensions, the isotropic angular mean of `v_x²` is one half of the squared radial
velocity.  The factor `1/2` is the explicit full-circle `cos² θ` average. -/
theorem isotropicMeanSquareRadialGroupVelocityX_eq
    (v m p : ℝ) :
    isotropicMeanSquareRadialGroupVelocityX v m p =
      radialEnergyDerivative v m p ^ 2 / 2 := by
  unfold isotropicMeanSquareRadialGroupVelocityX radialGroupVelocityX
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_cos_sq_zero_two_pi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

end

end AnomalousHall.MassiveDirac
