import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional polar Fourier transform

This module owns the representation-independent scalar Fourier transform used when a two-dimensional
physical-momentum integral is written in polar coordinates with a finite radial cutoff. The transform
includes the physical continuum normalization `d²p / (2πℏ)²` and the polar Jacobian `p`, while the
consumer supplies the momentum-space scalar field. The Cartesian Fourier phase itself is inherited
from the dimension-independent `Analysis.FourierGeometry` layer; this module owns only its
two-dimensional polar specialization and angular reduction.

The full-angle kernels below are the canonical intermediate for radial Fourier reduction. Constant,
first, and second angular channels are supplied through `AngularHarmonicCoefficients`, shared with
ordinary angular integration. The kernels remain explicit finite interval integrals rather than
being identified with Bessel functions; the pinned Mathlib revision does not provide that API.

No model Hamiltonian, matrix representation, disorder approximation, real-space cutoff, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Two-dimensional polar point `(ρ cos φ, ρ sin φ)`. -/
def polarPoint2D (radius angle : ℝ) : Fin 2 → ℝ :=
  ![radius * Real.cos angle, radius * Real.sin angle]

/-- The two-dimensional polar point is the generic finite-dimensional radial scaling specialized to
its usual unit direction `(cos φ, sin φ)`. -/
theorem polarPoint2D_eq_radialPoint (radius angle : ℝ) :
    polarPoint2D radius angle =
      radialPoint radius ![Real.cos angle, Real.sin angle] := by
  funext i
  fin_cases i <;> simp [polarPoint2D, radialPoint]

/-- Negating the radius negates a two-dimensional polar point at fixed angle. -/
theorem neg_polarPoint2D (radius angle : ℝ) :
    -(polarPoint2D radius angle) = polarPoint2D (-radius) angle := by
  rw [polarPoint2D_eq_radialPoint, polarPoint2D_eq_radialPoint,
    radialPoint_neg_radius]

/-- Fourier phase `exp(i p·r / ℏ)` for polar momentum `(p cos θ, p sin θ)` in two dimensions. -/
def physicalMomentumPolarFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  physicalMomentumFourierPhase hbar (polarPoint2D p θ) r

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- The physical polar Fourier phase at a polar real-space point depends only on the angular
difference `θ - φ`. -/
theorem physicalMomentumPolarFourierPhase_polarPoint2D
    (hbar p θ radius angle : ℝ) :
    physicalMomentumPolarFourierPhase hbar p θ (polarPoint2D radius angle) =
      polarFourierRadialPhase (p * radius / hbar) (θ - angle) := by
  unfold physicalMomentumPolarFourierPhase physicalMomentumFourierPhase polarFourierRadialPhase
  simp only [polarPoint2D, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.cos_sub]
  apply congrArg Complex.exp
  push_cast
  ring_nf

/-- Zeroth full-angle radial Fourier kernel. At a Mathlib revision with Bessel support this is the
integral representation that can be identified with `2π J₀(z)`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel. At a Mathlib revision with Bessel support this is
the integral representation that can be identified with `2π i J₁(z)`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  have h := integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi)
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using h
/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)` polynomial needed by
quadratic angular products. At a Mathlib revision with Bessel support this can be identified with
`-2π J₂(z)`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

@[fun_prop]
theorem continuous_polarFourierZerothAngularKernel :
    Continuous polarFourierZerothAngularKernel := by
  unfold polarFourierZerothAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierFirstCosineAngularKernel :
    Continuous polarFourierFirstCosineAngularKernel := by
  unfold polarFourierFirstCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierSecondCosineAngularKernel :
    Continuous polarFourierSecondCosineAngularKernel := by
  unfold polarFourierSecondCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

/-- Derivative of the dimensionless radial Fourier phase with respect to the polar angle. -/
private theorem polarFourierRadialPhase_hasDerivAt (z θ : ℝ) :
    HasDerivAt (polarFourierRadialPhase z)
      ((-Complex.I * (z : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
        polarFourierRadialPhase z θ) θ := by
  have hcos : HasDerivAt (fun t : ℝ => ((z * Real.cos t : ℝ) : ℂ))
      ((-z * Real.sin θ : ℝ) : ℂ) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul z).ofReal_comp
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * ((z * Real.cos t : ℝ) : ℂ))
      (Complex.I * ((-z * Real.sin θ : ℝ) : ℂ)) θ :=
    hcos.const_mul Complex.I
  have hphase := (Complex.hasDerivAt_exp _).comp θ harg
  convert hphase using 1
  · rfl
  · push_cast
    ring

/-- Angular integration by parts: the first Fourier harmonic is constrained by the
zeroth and second harmonics without assuming nonzero radial argument.

With the unnormalized kernels used by the physical Fourier measure, this is
`2 K1(z) = i z (K0(z) - K2(z))`. In Bessel notation this is the
`J0 + J2 = 2 J1/z` recurrence, stated without division by `z`. -/
theorem polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second (z : ℝ) :
    2 * polarFourierFirstCosineAngularKernel z =
      Complex.I * (z : ℂ) *
        (polarFourierZerothAngularKernel z - polarFourierSecondCosineAngularKernel z) := by
  let phase : ℝ → ℂ := polarFourierRadialPhase z
  let sine : ℝ → ℂ := fun θ => ((Real.sin θ : ℝ) : ℂ)
  let cosine : ℝ → ℂ := fun θ => ((Real.cos θ : ℝ) : ℂ)
  have hsin : ∀ θ : ℝ, HasDerivAt sine (cosine θ) θ := by
    intro θ
    simpa [sine, cosine] using (Real.hasDerivAt_sin θ).ofReal_comp
  have hphase : ∀ θ : ℝ, HasDerivAt phase
      ((-Complex.I * (z : ℂ) * sine θ) * phase θ) θ := by
    intro θ
    exact polarFourierRadialPhase_hasDerivAt z θ
  have hzero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ +
          sine θ * ((-Complex.I * (z : ℂ) * sine θ) * phase θ)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := sine) (v := phase) (u' := cosine)
      (v' := fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ)
      (fun θ _ => hsin θ) (fun θ _ => hphase θ)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    simpa [sine, cosine] using h
  have hcosInt : IntervalIntegrable (fun θ : ℝ => cosine θ * phase θ)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsinSqInt : IntervalIntegrable
      (fun θ : ℝ => phase θ * sine θ ^ 2) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfirst :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), cosine θ * phase θ) =
        (Complex.I * (z : ℂ)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) := by
    have h' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ -
          (Complex.I * (z : ℂ)) * (phase θ * sine θ ^ 2)) = 0 := by
      convert hzero using 1
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    rw [intervalIntegral.integral_sub hcosInt (hsinSqInt.const_mul _),
      intervalIntegral.integral_const_mul, sub_eq_zero] at h'
    exact h'
  have htrig (θ : ℝ) :
      2 * (phase θ * sine θ ^ 2) =
        phase θ -
          phase θ * (cosine θ ^ 2 - sine θ ^ 2) := by
    have h : sine θ ^ 2 + cosine θ ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    linear_combination (phase θ) * h
  have hsecond :
      2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) =
        polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z := by
    calc
      2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            2 * (phase θ * sine θ ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
            phase θ - phase θ * (cosine θ ^ 2 - sine θ ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact htrig θ
      _ = polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z := by
        rw [intervalIntegral.integral_sub]
        · rfl
        · apply Continuous.intervalIntegrable
          fun_prop
        · apply Continuous.intervalIntegrable
          fun_prop
  have hfirstKernel :
      polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) := by
    rw [polarFourierFirstCosineAngularKernel]
    convert hfirst using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [cosine, phase, mul_comm]
  calc
    2 * polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2)) := by
      rw [hfirstKernel]
      ring
    _ = _ := by rw [hsecond]

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hneg :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            unfold f polarFourierRadialPhase
            dsimp
            rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
            push_cast
            ring
      _ = -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
        rw [intervalIntegral.integral_neg]
  have hself :
      -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
    hneg.symm.trans hsub
  have hz : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 :=
    CharZero.neg_eq_self_iff.mp hself
  simpa [f] using hz

/-- The mixed quadratic harmonic `cos θ sin θ` vanishes against the radial Fourier phase over one
full angle. -/
theorem integral_polarFourierRadialPhase_mul_cos_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ *
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) = 0 := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ *
      (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hneg :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            unfold f polarFourierRadialPhase
            dsimp
            rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
            push_cast
            ring
      _ = -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
        rw [intervalIntegral.integral_neg]
  have hself :
      -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
    hneg.symm.trans hsub
  have hz : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 :=
    CharZero.neg_eq_self_iff.mp hself
  simpa [f] using hz

/-- Phase-weighted full-angle integration of the canonical constant/first/second harmonic
decomposition. The first-sine and mixed-second channels vanish on the radial axis. -/
theorem AngularHarmonicCoefficients.integral_polarFourierRadialPhase
    (coefficients : AngularHarmonicCoefficients ℂ) (z p : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
  have hphase : Continuous fun θ : ℝ => polarFourierRadialPhase z θ := by
    unfold polarFourierRadialPhase
    fun_prop
  have hcos : Continuous fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) := by
    fun_prop
  have hsin : Continuous fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) := by
    fun_prop
  have hA : IntervalIntegrable
      (fun θ : ℝ => polarFourierRadialPhase z θ * coefficients.constant)
      volume 0 (2 * Real.pi) :=
    (hphase.mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hB : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) * coefficients.firstCosine)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hcos).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) * coefficients.firstSine)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hsin).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hD : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ *
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))) *
            coefficients.secondCosine) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hE : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ *
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) * coefficients.secondMixed)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
        (p : ℂ) *
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
            polarFourierRadialPhase z θ * coefficients.constant +
              (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) *
                coefficients.firstCosine +
              (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) *
                coefficients.firstSine +
              (polarFourierRadialPhase z θ *
                ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))) *
                coefficients.secondCosine +
              (polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) *
                coefficients.secondMixed := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          simp only [AngularHarmonicCoefficients.eval, smul_eq_mul]
          ring
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
      rw [intervalIntegral.integral_add (((hA.add hB).add hC).add hD) hE,
        intervalIntegral.integral_add ((hA.add hB).add hC) hD,
        intervalIntegral.integral_add (hA.add hB) hC,
        intervalIntegral.integral_add hA hB,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        integral_polarFourierRadialPhase_mul_sin_zero,
        integral_polarFourierRadialPhase_mul_cos_mul_sin_zero]
      simp [polarFourierZerothAngularKernel, polarFourierFirstCosineAngularKernel,
        polarFourierSecondCosineAngularKernel]

/-- Full-angle reduction for a scalar field containing only constant and first sine/cosine
harmonics. The sine harmonic drops out on the radial axis, leaving the zeroth and first-cosine
kernels that later become the `J₀` and `J₁` channels. -/
theorem integral_polarFourierRadialPhase_first_harmonics
    (z p : ℝ) (a b c : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z * b) := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := a
      firstCosine := b
      firstSine := c
      secondCosine := 0
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
    coefficients.integral_polarFourierRadialPhase z p

private theorem intervalIntegral_fullPeriod_comp_sub_eq
    (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h := hf.intervalIntegral_add_eq (-angle) 0
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- Reversing the radial Fourier argument is equivalent to shifting the polar angle by π. -/
private theorem polarFourierRadialPhase_neg_eq_shift_pi (z θ : ℝ) :
    polarFourierRadialPhase (-z) θ =
      polarFourierRadialPhase z (θ - Real.pi) := by
  unfold polarFourierRadialPhase
  apply congrArg Complex.exp
  rw [Real.cos_sub_pi]
  push_cast
  ring

/-- The zeroth full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierZerothAngularKernel_neg (z : ℝ) :
    polarFourierZerothAngularKernel (-z) =
      polarFourierZerothAngularKernel z := by
  let f : ℝ → ℂ := fun θ => polarFourierRadialPhase z θ
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi]
  unfold polarFourierZerothAngularKernel
  simp_rw [polarFourierRadialPhase_neg_eq_shift_pi]
  simpa [f] using intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi

/-- The first-cosine full-angle radial Fourier kernel is odd in its radial argument. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_neg (z : ℝ) :
    polarFourierFirstCosineAngularKernel (-z) =
      -polarFourierFirstCosineAngularKernel z := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi]
  have hpoint (θ : ℝ) :
      polarFourierRadialPhase (-z) θ * ((Real.cos θ : ℝ) : ℂ) =
        -f (θ - Real.pi) := by
    rw [polarFourierRadialPhase_neg_eq_shift_pi]
    dsimp [f]
    rw [Real.cos_sub_pi]
    push_cast
    ring
  unfold polarFourierFirstCosineAngularKernel
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg,
    intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi]

/-- The second-cosine full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_neg (z : ℝ) :
    polarFourierSecondCosineAngularKernel (-z) =
      polarFourierSecondCosineAngularKernel z := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hpoint (θ : ℝ) :
      polarFourierRadialPhase (-z) θ *
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) =
        f (θ - Real.pi) := by
    rw [polarFourierRadialPhase_neg_eq_shift_pi]
    dsimp [f]
    rw [Real.cos_sub_pi, Real.sin_sub_pi]
    push_cast
    ring
  unfold polarFourierSecondCosineAngularKernel
  simp_rw [hpoint]
  simpa [f] using intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi

/-- Complex conjugation of the angular Fourier phase reverses its radial argument. -/
private theorem polarFourierRadialPhase_conj (z θ : ℝ) :
    conj (polarFourierRadialPhase z θ) =
      polarFourierRadialPhase (-z) θ := by
  unfold polarFourierRadialPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Complex conjugation commutes with full-angle integration. -/
private theorem integral_polarFourier_conj (f : ℝ → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (f θ)) =
      conj (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) := by
  simpa using (Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
    (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi)

/-- The zeroth angular Fourier kernel is real for real radial arguments. -/
@[simp] theorem polarFourierZerothAngularKernel_conj (z : ℝ) :
    conj (polarFourierZerothAngularKernel z) =
      polarFourierZerothAngularKernel z := by
  calc
    conj (polarFourierZerothAngularKernel z) =
        polarFourierZerothAngularKernel (-z) := by
      unfold polarFourierZerothAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      exact polarFourierRadialPhase_conj z θ
    _ = polarFourierZerothAngularKernel z := polarFourierZerothAngularKernel_neg z

/-- The first cosine angular Fourier kernel is purely imaginary for real radial arguments. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_conj (z : ℝ) :
    conj (polarFourierFirstCosineAngularKernel z) =
      -polarFourierFirstCosineAngularKernel z := by
  calc
    conj (polarFourierFirstCosineAngularKernel z) =
        polarFourierFirstCosineAngularKernel (-z) := by
      unfold polarFourierFirstCosineAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [map_mul, Complex.conj_ofReal, polarFourierRadialPhase_conj]
    _ = -polarFourierFirstCosineAngularKernel z := polarFourierFirstCosineAngularKernel_neg z

/-- The second cosine angular Fourier kernel is real for real radial arguments. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_conj (z : ℝ) :
    conj (polarFourierSecondCosineAngularKernel z) =
      polarFourierSecondCosineAngularKernel z := by
  calc
    conj (polarFourierSecondCosineAngularKernel z) =
        polarFourierSecondCosineAngularKernel (-z) := by
      unfold polarFourierSecondCosineAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal,
        polarFourierRadialPhase_conj]
    _ = polarFourierSecondCosineAngularKernel z := polarFourierSecondCosineAngularKernel_neg z

private theorem angular_second_harmonics_add
    (angle θ : ℝ) (a b c d e : ℂ) :
    a + ((Real.cos (θ + angle) : ℝ) : ℂ) * b +
          ((Real.sin (θ + angle) : ℝ) : ℂ) * c +
          ((((Real.cos (θ + angle) : ℝ) : ℂ) ^ 2) -
            (((Real.sin (θ + angle) : ℝ) : ℂ) ^ 2)) * d +
          (((Real.cos (θ + angle) : ℝ) : ℂ) *
            ((Real.sin (θ + angle) : ℝ) : ℂ)) * e =
      a + ((Real.cos θ : ℝ) : ℂ) *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          ((Real.sin θ : ℝ) : ℂ) *
            (-((Real.sin angle : ℝ) : ℂ) * b + ((Real.cos angle : ℝ) : ℂ) * c) +
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e) +
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
            ((-4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ))) * d +
              (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * e)) := by
  rw [Real.cos_add, Real.sin_add]
  push_cast
  ring

private theorem integral_polarFourierRadialPhase_shifted_second_harmonics
    (z p angle : ℝ) (a b c d e : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
  let f : ℝ → ℂ := fun α =>
    ((p : ℂ) * polarFourierRadialPhase z α) *
      (a + ((Real.cos (α + angle) : ℝ) : ℂ) * b +
        ((Real.sin (α + angle) : ℝ) : ℂ) * c +
        ((((Real.cos (α + angle) : ℝ) : ℂ) ^ 2) -
          (((Real.sin (α + angle) : ℝ) : ℂ) ^ 2)) * d +
        (((Real.cos (α + angle) : ℝ) : ℂ) *
          ((Real.sin (α + angle) : ℝ) : ℂ)) * e)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro α
    simp only [f, polarFourierRadialPhase]
    rw [Real.cos_add_two_pi]
    have hangle : α + 2 * Real.pi + angle = (α + angle) + 2 * Real.pi := by
      ring
    rw [hangle, Real.cos_add_two_pi, Real.sin_add_two_pi]
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
          (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
            ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
            (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle) := by
          apply intervalIntegral.integral_congr
          intro θ _
          simp [f]
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
      intervalIntegral_fullPeriod_comp_sub_eq f hf angle
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
      simp_rw [f, angular_second_harmonics_add]
      let coefficients : AngularHarmonicCoefficients ℂ :=
        { constant := a
          firstCosine :=
            ((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c
          firstSine :=
            -((Real.sin angle : ℝ) : ℂ) * b + ((Real.cos angle : ℝ) : ℂ) * c
          secondCosine :=
            (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * d +
              ((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ) * e
          secondMixed :=
            -4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * d +
              (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * e }
      simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
        coefficients.integral_polarFourierRadialPhase z p

/-- Phase-weighted full-angle reduction of canonical harmonic coefficients at an arbitrary
real-space polar angle. -/
theorem AngularHarmonicCoefficients.integral_polarFourierRadialPhase_shifted
    (coefficients : AngularHarmonicCoefficients ℂ) (z p angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * coefficients.firstCosine +
              ((Real.sin angle : ℝ) : ℂ) * coefficients.firstSine) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * coefficients.secondCosine +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                coefficients.secondMixed)) := by
  simpa [AngularHarmonicCoefficients.eval, smul_eq_mul] using
    (integral_polarFourierRadialPhase_shifted_second_harmonics
      z p angle coefficients.constant coefficients.firstCosine coefficients.firstSine
      coefficients.secondCosine coefficients.secondMixed)

/-- Finite-cutoff polar Fourier transform of a complex scalar momentum field with the physical
momentum measure `d²p / (2πℏ)²` included exactly once. -/
noncomputable def finiteCutoffPhysicalMomentumPolarFourier
    (hbar pMax : ℝ) (field : ℝ → ℝ → ℂ) (r : Fin 2 → ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * physicalMomentumPolarFourierPhase hbar p θ r) * field p θ

/-- Finite-cutoff polar Fourier reduction of canonical harmonic coefficients at an arbitrary polar
real-space point. -/
theorem finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
    (hbar pMax radius angle : ℝ) (coefficients : ℝ → AngularHarmonicCoefficients ℂ) :
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ => (coefficients p).eval θ) (polarPoint2D radius angle) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) * (coefficients p).constant +
              polarFourierFirstCosineAngularKernel (p * radius / hbar) *
                (((Real.cos angle : ℝ) : ℂ) * (coefficients p).firstCosine +
                  ((Real.sin angle : ℝ) : ℂ) * (coefficients p).firstSine) +
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                    (((Real.sin angle : ℝ) : ℂ) ^ 2)) * (coefficients p).secondCosine +
                  (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                    (coefficients p).secondMixed)) := by
  unfold finiteCutoffPhysicalMomentumPolarFourier
  apply congrArg (((momentumMeasurePrefactor hbar : ℝ) : ℂ) * ·)
  apply intervalIntegral.integral_congr
  intro p _
  simp_rw [physicalMomentumPolarFourierPhase_polarPoint2D]
  exact (coefficients p).integral_polarFourierRadialPhase_shifted
    (p * radius / hbar) p angle

end

end Transport
end QuantumTheory
