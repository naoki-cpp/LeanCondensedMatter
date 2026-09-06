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

The reusable coefficient and operator identities are owned at arbitrary signed regulator. Physical
retarded/advanced consumers specialize through `SpectralSide.regulator` only where branch semantics
are actually needed. No radial integration, disorder normalization, UV limit, or zero-broadening
limit is introduced here.
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

/-- Polar-angle dependence of every Pauli-vector Green coefficient. The `y` channel shares the
positive-x-axis radial amplitude of the `x` channel, while the `z` channel is angle independent. -/
theorem pauliGreenPauliCoefficientOfRegulator_polar
    (axis : PauliAxis) (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenPauliCoefficientOfRegulator
        axis v m (p * Real.cos θ) (p * Real.sin θ) probeEnergy regulator =
      match axis with
      | .x => ((Real.cos θ : ℝ) : ℂ) *
          pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator
      | .y => ((Real.sin θ : ℝ) : ℂ) *
          pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator
      | .z => pauliGreenPauliCoefficientOfRegulator .z v m p 0 probeEnergy regulator := by
  cases axis <;>
    simp [pauliGreenPauliCoefficientOfRegulator, pauliAxisComponent,
      pauliGreenDenominatorOfRegulator_polar] <;>
    ring

/-- Exact polar-angle decomposition of the arbitrary-regulator clean Green operator. -/
theorem pauliGreenOperatorOfRegulator_polar_eq
    (v m p θ probeEnergy regulator : ℝ) :
    pauliGreenOperatorOfRegulator v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy regulator =
      inversionSymmetrizedPauliGreenOperatorOfRegulator v m p 0 probeEnergy regulator +
        (((Real.cos θ : ℝ) : ℂ) •
          (pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator •
            matrixOperator sigmaX)) +
        (((Real.sin θ : ℝ) : ℂ) •
          (pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator •
            matrixOperator sigmaY)) := by
  rw [inversionSymmetrizedPauliGreenOperatorOfRegulator_eq_evenChannels]
  rw [pauliGreenOperatorOfRegulator]
  rw [pauliGreenScalarCoefficientOfRegulator_polar,
    pauliGreenPauliCoefficientOfRegulator_polar .x,
    pauliGreenPauliCoefficientOfRegulator_polar .y,
    pauliGreenPauliCoefficientOfRegulator_polar .z]
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
    pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator •
      matrixOperator sigmaX
  let yPart : DiracHilbert →L[ℂ] DiracHilbert :=
    pauliGreenPauliCoefficientOfRegulator .x v m p 0 probeEnergy regulator •
      matrixOperator sigmaY
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
