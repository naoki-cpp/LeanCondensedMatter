import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Basic
import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Radial kinematics of the two-dimensional massive Dirac model

This file owns radial dispersion facts shared by longitudinal response and the Bastin radial-energy
bridge. These facts depend only on the clean massive-Dirac spectrum; occupation and transport
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
`cos θ` factor. Its full-angle mean square uses the model-independent harmonic integral owned by
`Transport.Analysis.AngularHarmonics`.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

/-- The positive Dirac energy is nonnegative for every momentum. -/
theorem energy_nonneg (v m px py : ℝ) :
    0 ≤ energy v m px py := by
  exact Real.sqrt_nonneg _

/-- For nonnegative mass, the massive-Dirac energy is bounded below by the mass uniformly in
momentum. -/
theorem mass_le_energy (v m px py : ℝ) (_hm : 0 ≤ m) :
    m ≤ energy v m px py := by
  have hkin : 0 ≤ v ^ 2 * (px ^ 2 + py ^ 2) := by
    positivity
  have hsq : m ^ 2 ≤ energy v m px py ^ 2 := by
    rw [energy_sq]
    unfold energySq
    linarith
  have hE := energy_nonneg v m px py
  nlinarith [_hm]

/-- For positive mass the model stays uniformly away from the Dirac degeneracy. -/
theorem energy_pos_of_mass_pos (v m px py : ℝ) (hm : 0 < m) :
    0 < energy v m px py := by
  exact lt_of_lt_of_le hm (mass_le_energy v m px py hm.le)

/-- Radial derivative of the positive massive-Dirac energy. -/
def radialEnergyDerivative (v m p : ℝ) : ℝ :=
  v ^ 2 * p / energy v m p 0

/-- The positive radial massive-Dirac dispersion has derivative `v² p / E` when `m > 0`. -/
theorem hasDerivAt_energy_radial
    (v m p : ℝ) (hm : 0 < m) :
    HasDerivAt (fun q : ℝ => energy v m q 0) (radialEnergyDerivative v m p) p := by
  have hpow : HasDerivAt (fun q : ℝ => q ^ 2) (2 * p) p := by
    simpa using (hasDerivAt_pow 2 p)
  have hmul :
      HasDerivAt (fun q : ℝ => v ^ 2 * q ^ 2) (v ^ 2 * (2 * p)) p := by
    exact HasDerivAt.const_mul (v ^ 2) hpow
  have hpoly :
      HasDerivAt (fun q : ℝ => energySq v m q 0) (v ^ 2 * (2 * p)) p := by
    simpa [energySq] using hmul.add_const (m ^ 2)
  have hsq_ne : energySq v m p 0 ≠ 0 := by
    unfold energySq
    positivity
  have hsqrt := hpoly.sqrt hsq_ne
  unfold radialEnergyDerivative energy
  convert hsqrt using 1
  field_simp [ne_of_gt (energy_pos_of_mass_pos v m p 0 hm)]

/-- The radial energy derivative is continuous for positive mass. -/
theorem continuous_radialEnergyDerivative
    (v m : ℝ) (hm : 0 < m) :
    Continuous (radialEnergyDerivative v m) := by
  unfold radialEnergyDerivative
  have hE : Continuous (fun p : ℝ => energy v m p 0) := by
    unfold energy energySq
    fun_prop
  exact (continuous_const.mul continuous_id).div hE
    (fun p => ne_of_gt (energy_pos_of_mass_pos v m p 0 hm))

/-- `x` component obtained by projecting the radial group velocity onto polar angle `θ`. -/
def radialGroupVelocityX (v m p θ : ℝ) : ℝ :=
  radialEnergyDerivative v m p * Real.cos θ

/-- Full-angle mean square of the `x` component of the radial group velocity. -/
def isotropicMeanSquareRadialGroupVelocityX (v m p : ℝ) : ℝ :=
  (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), radialGroupVelocityX v m p θ ^ 2) /
    (2 * Real.pi)

/-- In two dimensions, the isotropic angular mean of `v_x²` is one half of the squared radial
velocity. The factor `1/2` is the generic full-circle `cos² θ` average. -/
theorem isotropicMeanSquareRadialGroupVelocityX_eq
    (v m p : ℝ) :
    isotropicMeanSquareRadialGroupVelocityX v m p =
      radialEnergyDerivative v m p ^ 2 / 2 := by
  unfold isotropicMeanSquareRadialGroupVelocityX radialGroupVelocityX
  have hfun :
      (fun θ : ℝ => (radialEnergyDerivative v m p * Real.cos θ) ^ 2) =
        fun θ : ℝ => radialEnergyDerivative v m p ^ 2 * Real.cos θ ^ 2 := by
    funext θ
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_cos_sq_zero_two_pi]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

end

end AnomalousHall.MassiveDirac
