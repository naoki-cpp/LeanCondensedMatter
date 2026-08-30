import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.PropagatorSymmetry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Angular reduction of the massive-Dirac continuum Green operator

This file supplies the missing bridge between the two-dimensional continuum momentum integral and
its radial form.  For polar momentum

```text
pₓ = p cos θ,   pᵧ = p sin θ,
```

the scalar and `σ_z` Green coefficients are independent of `θ`, while the in-plane Pauli channels
are proportional to `cos θ` and `sin θ`.  Their explicit full-angle interval integrals therefore
vanish, and

```text
∫₀²π dθ G_s(p cos θ, p sin θ)
  = 2π (g₀(p,0) I + g_z(p,0) σ_z).
```

This theorem, rather than momentum inversion alone, justifies the `2π` angular factor used by the
finite-cutoff continuum Born self-energy.  No radial integration, disorder normalization, UV limit,
or zero-broadening limit is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Full-angle integral of the complexified first cosine harmonic. -/
theorem integral_complex_cos_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.cos θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.cos)

/-- Full-angle integral of the complexified first sine harmonic. -/
theorem integral_complex_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  simpa using
    (@intervalIntegral.integral_ofReal (0 : ℝ) (2 * Real.pi) volume Real.sin)

/-- The complexified second cosine harmonic integrates to zero over a full polar angle. -/
theorem integral_complex_cos_sq_sub_sin_sq_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℂ) ^ 2) - ((Real.sin θ : ℂ) ^ 2)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos θ ^ 2 - Real.sin θ ^ 2 : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            rfl
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.cos θ ^ 2 - Real.sin θ ^ 2) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.cos θ ^ 2 - Real.sin θ ^ 2)
    _ = 0 := by
      rw [integral_cos_sq_sub_sin_sq]
      simp

/-- The complexified mixed second harmonic integrates to zero over a full polar angle. -/
theorem integral_complex_cos_mul_sin_zero_two_pi :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) =
        (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          (((Real.sin θ * Real.cos θ : ℝ) : ℂ))) := by
            apply intervalIntegral.integral_congr
            intro θ _
            push_cast
            ring
    _ = (((∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          Real.sin θ * Real.cos θ) : ℝ) : ℂ) := by
            exact @intervalIntegral.integral_ofReal
              (0 : ℝ) (2 * Real.pi) volume
              (fun θ : ℝ => Real.sin θ * Real.cos θ)
    _ = 0 := by
      rw [integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := 2 * Real.pi) 1 0]
      simp

/-- The massive-Dirac dispersion is radial in polar momentum coordinates. -/
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

/-- The Green denominator is independent of the polar angle. -/
@[simp] theorem pauliGreenDenominator_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenDenominator side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      pauliGreenDenominator side v m p 0 probeEnergy broadening := by
  simp [pauliGreenDenominator]

/-- The scalar Green coefficient is independent of the polar angle. -/
@[simp] theorem pauliGreenScalarCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenScalarCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      pauliGreenScalarCoefficient side v m p 0 probeEnergy broadening := by
  simp [pauliGreenScalarCoefficient]

/-- The `σ_z` Green coefficient is independent of the polar angle. -/
@[simp] theorem pauliGreenZCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenZCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      pauliGreenZCoefficient side v m p 0 probeEnergy broadening := by
  simp [pauliGreenZCoefficient]

/-- The `σₓ` coefficient carries the polar factor `cos θ`. -/
theorem pauliGreenXCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenXCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      ((Real.cos θ : ℝ) : ℂ) *
        pauliGreenXCoefficient side v m p 0 probeEnergy broadening := by
  simp [pauliGreenXCoefficient]
  ring

/-- The `σᵧ` coefficient carries the polar factor `sin θ`, with the same radial amplitude as the
`σₓ` coefficient on the positive x axis. -/
theorem pauliGreenYCoefficient_polar
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenYCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      ((Real.sin θ : ℝ) : ℂ) *
        pauliGreenXCoefficient side v m p 0 probeEnergy broadening := by
  simp [pauliGreenYCoefficient, pauliGreenXCoefficient]
  ring

/-- Exact polar-angle decomposition of the clean Green operator. -/
theorem pauliGreenOperator_polar_eq
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenOperator side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      inversionSymmetrizedPauliGreenOperator side v m p 0 probeEnergy broadening +
        (((Real.cos θ : ℝ) : ℂ) •
          (pauliGreenXCoefficient side v m p 0 probeEnergy broadening • matrixOperator sigmaX)) +
        (((Real.sin θ : ℝ) : ℂ) •
          (pauliGreenXCoefficient side v m p 0 probeEnergy broadening • matrixOperator sigmaY)) := by
  rw [inversionSymmetrizedPauliGreenOperator_eq_evenChannels]
  rw [pauliGreenOperator]
  rw [pauliGreenScalarCoefficient_polar, pauliGreenXCoefficient_polar,
    pauliGreenYCoefficient_polar, pauliGreenZCoefficient_polar]
  module

/-- Full polar-angle integral of the clean Green operator at fixed radial momentum. -/
noncomputable def continuumAngularGreenIntegral
    (side : SpectralSide) (v m p probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    pauliGreenOperator side v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy broadening

/-- Explicit angular integration removes both in-plane Pauli channels and produces the factor
`2π` multiplying the inversion-even `I + σ_z` operator. -/
theorem continuumAngularGreenIntegral_eq
    (side : SpectralSide) (v m p probeEnergy broadening : ℝ) :
    continuumAngularGreenIntegral side v m p probeEnergy broadening =
      (2 * Real.pi) •
        inversionSymmetrizedPauliGreenOperator side v m p 0 probeEnergy broadening := by
  let even : DiracHilbert →L[ℂ] DiracHilbert :=
    inversionSymmetrizedPauliGreenOperator side v m p 0 probeEnergy broadening
  let xPart : DiracHilbert →L[ℂ] DiracHilbert :=
    pauliGreenXCoefficient side v m p 0 probeEnergy broadening • matrixOperator sigmaX
  let yPart : DiracHilbert →L[ℂ] DiracHilbert :=
    pauliGreenXCoefficient side v m p 0 probeEnergy broadening • matrixOperator sigmaY
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
  unfold continuumAngularGreenIntegral
  have hfun :
      (fun θ : ℝ =>
        pauliGreenOperator side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) =
        fun θ : ℝ =>
          even + ((Real.cos θ : ℝ) : ℂ) • xPart + ((Real.sin θ : ℝ) : ℂ) • yPart := by
    funext θ
    exact pauliGreenOperator_polar_eq side v m p θ probeEnergy broadening
  rw [hfun]
  rw [intervalIntegral.integral_add (heven.add hx) hy]
  rw [intervalIntegral.integral_add heven hx]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const]
  rw [integral_complex_cos_zero_two_pi, integral_complex_sin_zero_two_pi]
  simp [even]

end

end AnomalousHall.MassiveDirac
