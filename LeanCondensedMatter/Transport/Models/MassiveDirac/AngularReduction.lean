import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Kinematics
import LeanCondensedMatter.Transport.Models.MassiveDirac.PropagatorSymmetry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Angular reduction of the massive-Dirac continuum Green operator

This file supplies the bridge between the two-dimensional continuum momentum integral and its radial
form. The analytic owner is the Green operator at an arbitrary signed regulator `γ`. For polar
momentum

```text
pₓ = p cos θ,   pᵧ = p sin θ,
```

the scalar and `σ_z` Green coefficients are independent of `θ`, while the in-plane Pauli channels
are proportional to `cos θ` and `sin θ`. Their explicit full-angle interval integrals vanish, so

```text
∫₀²π dθ G(E, γ; p cos θ, p sin θ)
  = 2π (g₀(p,0) I + g_z(p,0) σ_z).
```

Physical side-indexed coefficient lemmas are retained where they are shared by downstream vertex
calculations; the operator-valued angular integral itself is owned only at arbitrary regulator.
No radial integration, disorder normalization, UV limit, or zero-broadening limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

@[simp] theorem pauliGreenDenominatorOfRegulator_polar
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenDenominatorOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator := by
  simp [pauliGreenDenominatorOfRegulator]

@[simp] theorem pauliGreenScalarCoefficientOfRegulator_polar
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenScalarCoefficientOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      pauliGreenScalarCoefficientOfRegulator v m p 0 probeEnergy regulator := by
  simp [pauliGreenScalarCoefficientOfRegulator]

@[simp] theorem pauliGreenZCoefficientOfRegulator_polar
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenZCoefficientOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      pauliGreenZCoefficientOfRegulator v m p 0 probeEnergy regulator := by
  simp [pauliGreenZCoefficientOfRegulator]

/-- The arbitrary-regulator `σₓ` coefficient carries the polar factor `cos θ`. -/
theorem pauliGreenXCoefficientOfRegulator_polar
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenXCoefficientOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      ((Real.cos θ : ℝ) : ℂ) *
        pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator := by
  rw [pauliGreenXCoefficientOfRegulator, pauliGreenXCoefficientOfRegulator]
  rw [pauliGreenDenominatorOfRegulator_polar]
  push_cast
  ring

/-- The arbitrary-regulator `σᵧ` coefficient carries the polar factor `sin θ`, with the same radial
amplitude as the `σₓ` coefficient on the positive x axis. -/
theorem pauliGreenYCoefficientOfRegulator_polar
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenYCoefficientOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      ((Real.sin θ : ℝ) : ℂ) *
        pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator := by
  rw [pauliGreenYCoefficientOfRegulator, pauliGreenXCoefficientOfRegulator]
  rw [pauliGreenDenominatorOfRegulator_polar]
  push_cast
  ring

/-- Physical-side scalar coefficient radiality, retained for downstream side-indexed consumers. -/
@[simp] theorem pauliGreenScalarCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenScalarCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      pauliGreenScalarCoefficient side v m p 0 probeEnergy broadening := by
  simpa [pauliGreenScalarCoefficient] using
    pauliGreenScalarCoefficientOfRegulator_polar
      v m p θ probeEnergy (side.regulator broadening)

/-- Physical-side `σ_z` coefficient radiality, retained for downstream side-indexed consumers. -/
@[simp] theorem pauliGreenZCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenZCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      pauliGreenZCoefficient side v m p 0 probeEnergy broadening := by
  simpa [pauliGreenZCoefficient] using
    pauliGreenZCoefficientOfRegulator_polar
      v m p θ probeEnergy (side.regulator broadening)

/-- Physical-side `σₓ` polar factor, retained for downstream side-indexed consumers. -/
theorem pauliGreenXCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenXCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      ((Real.cos θ : ℝ) : ℂ) *
        pauliGreenXCoefficient side v m p 0 probeEnergy broadening := by
  simpa [pauliGreenXCoefficient] using
    pauliGreenXCoefficientOfRegulator_polar
      v m p θ probeEnergy (side.regulator broadening)

/-- Physical-side `σᵧ` polar factor, retained for downstream side-indexed consumers. -/
theorem pauliGreenYCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenYCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      ((Real.sin θ : ℝ) : ℂ) *
        pauliGreenXCoefficient side v m p 0 probeEnergy broadening := by
  simpa [pauliGreenYCoefficient, pauliGreenXCoefficient] using
    pauliGreenYCoefficientOfRegulator_polar
      v m p θ probeEnergy (side.regulator broadening)

/-- Exact polar-angle decomposition of the arbitrary-regulator clean Green operator. -/
theorem pauliGreenOperatorOfRegulator_polar_eq
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenOperatorOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      inversionSymmetrizedPauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator +
        (((Real.cos θ : ℝ) : ℂ) •
          (pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator •
            matrixOperator sigmaX)) +
        (((Real.sin θ : ℝ) : ℂ) •
          (pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator •
            matrixOperator sigmaY)) := by
  rw [inversionSymmetrizedPauliGreenOperatorOfRegulator_eq_evenChannels]
  rw [pauliGreenOperatorOfRegulator]
  rw [pauliGreenScalarCoefficientOfRegulator_polar,
    pauliGreenXCoefficientOfRegulator_polar,
    pauliGreenYCoefficientOfRegulator_polar,
    pauliGreenZCoefficientOfRegulator_polar]
  module

/-- Full polar-angle integral of the clean Green operator at fixed radial momentum and arbitrary
signed regulator. -/
noncomputable def continuumAngularGreenIntegralOfRegulator
    (v m p probeEnergy regulator : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    pauliGreenOperatorOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy regulator

/-- Explicit angular integration removes both in-plane Pauli channels and produces the factor `2π`
at arbitrary signed regulator. -/
theorem continuumAngularGreenIntegralOfRegulator_eq
    (v m p probeEnergy regulator : ℝ) :
    continuumAngularGreenIntegralOfRegulator v m p probeEnergy regulator =
      (2 * Real.pi) •
        inversionSymmetrizedPauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator := by
  let even : DiracHilbert →L[ℂ] DiracHilbert :=
    inversionSymmetrizedPauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator
  let xPart : DiracHilbert →L[ℂ] DiracHilbert :=
    pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator • matrixOperator sigmaX
  let yPart : DiracHilbert →L[ℂ] DiracHilbert :=
    pauliGreenXCoefficientOfRegulator v m p 0 probeEnergy regulator • matrixOperator sigmaY
  have hcos : Continuous (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_cos
  have hsin : Continuous (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sin
  have heven : IntervalIntegrable (fun _ : ℝ => even) volume 0 (2 * Real.pi) :=
    (continuous_const : Continuous (fun _ : ℝ => even)).intervalIntegrable 0 (2 * Real.pi)
  have hx : IntervalIntegrable
      (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) • xPart) volume 0 (2 * Real.pi) :=
    (hcos.smul (continuous_const : Continuous (fun _ : ℝ => xPart))).intervalIntegrable
      0 (2 * Real.pi)
  have hy : IntervalIntegrable
      (fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) • yPart) volume 0 (2 * Real.pi) :=
    (hsin.smul (continuous_const : Continuous (fun _ : ℝ => yPart))).intervalIntegrable
      0 (2 * Real.pi)
  unfold continuumAngularGreenIntegralOfRegulator
  simp_rw [pauliGreenOperatorOfRegulator_polar_eq v m p _ probeEnergy regulator]
  rw [intervalIntegral.integral_add (heven.add hx) hy]
  rw [intervalIntegral.integral_add heven hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp [even]

end

end QuantumTheory.Transport.Models.MassiveDirac
