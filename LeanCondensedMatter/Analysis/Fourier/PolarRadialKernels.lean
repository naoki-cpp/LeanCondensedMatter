import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.ZerothBessel
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Differentiation
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.ZerothDerivative
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.ThreeTermRecurrence
import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import LeanCondensedMatter.Analysis.Fourier.FullAngleCosineMoments
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Polar Fourier–Bessel kernel analysis

The core definitions and elementary properties live in
`Analysis.Fourier.PolarRadialKernels.Core`; the zeroth Bessel bridge is in
`Analysis.Fourier.PolarRadialKernels.ZerothBessel`. This module develops angular harmonics,
higher-harmonic Bessel identities, symmetries, differentiation formulas,
and full-period harmonic reduction. Differential identities for the kernels
are provided by `PolarRadialKernels.Differentiation` and the independent
`Bessel.ZerothDerivative` module. It assumes no momentum measure, Planck
constant, physical Fourier normalization, transport mechanism, or Hamiltonian.

The existing declaration namespace is preserved during the first file-ownership
migration to avoid a breaking repository-wide declaration rename. The mathematical
module itself depends only on Analysis and Mathlib.
-/

namespace QuantumTheory

open AngularHarmonics
namespace Transport

open BesselHypergeometric

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- The first angular Fourier harmonic is the correctly normalized Bessel function
`J₁`, for every real radial Fourier argument. -/
theorem polarFourierFirstCosineAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierFirstCosineAngularKernel z =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * Complex.besselJ 1 (z : ℂ) := by
  have hfun :
      (fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
        Complex.besselJ 0 (t : ℂ)) = polarFourierZerothAngularKernel := by
    funext t
    exact (polarFourierZerothAngularKernel_eq_besselJ t).symm
  have hJ := ((besselJ_zero_hasDerivAt (z : ℂ)).comp_ofReal).const_mul
    ((2 * Real.pi : ℝ) : ℂ)
  change HasDerivAt
    (fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 (t : ℂ))
    (((2 * Real.pi : ℝ) : ℂ) * -Complex.besselJ 1 (z : ℂ)) z at hJ
  rw [hfun] at hJ
  have hderiv := (polarFourierZerothAngularKernel_hasDerivAt z).unique hJ
  have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; ring
  calc
    polarFourierFirstCosineAngularKernel z =
        ((-Complex.I) * Complex.I) * polarFourierFirstCosineAngularKernel z := by
      rw [hI, one_mul]
    _ = (-Complex.I) * (Complex.I * polarFourierFirstCosineAngularKernel z) := by
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * Complex.besselJ 1 (z : ℂ) := by
      rw [hderiv]
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
  have hcphase : Continuous phase := by
    change Continuous (fun θ : ℝ =>
      Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))))
    fun_prop
  have hcsin : Continuous sine := by
    dsimp [sine]
    fun_prop
  have hccos : Continuous cosine := by
    dsimp [cosine]
    fun_prop
  have hcvprime : Continuous
      (fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ) :=
    ((continuous_const.mul hcsin).mul hcphase)
  have hsin : ∀ θ : ℝ, HasDerivAt sine (cosine θ) θ := by
    intro θ
    simpa [sine, cosine] using (Real.hasDerivAt_sin θ).ofReal_comp
  have hphase : ∀ θ : ℝ, HasDerivAt phase
      ((-Complex.I * (z : ℂ) * sine θ) * phase θ) θ :=
    polarFourierRadialPhase_hasDerivAt z
  have hzero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ +
          sine θ * ((-Complex.I * (z : ℂ) * sine θ) * phase θ)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := sine) (v := phase) (u' := cosine)
      (v' := fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ)
      (fun θ _ => hsin θ) (fun θ _ => hphase θ)
      (hccos.intervalIntegrable _ _)
      (hcvprime.intervalIntegrable _ _)
    simpa [sine, cosine] using h
  have hcosInt : IntervalIntegrable (fun θ : ℝ => cosine θ * phase θ)
      volume 0 (2 * Real.pi) :=
    (hccos.mul hcphase).intervalIntegrable _ _
  have hsinSqInt : IntervalIntegrable
      (fun θ : ℝ => phase θ * sine θ ^ 2) volume 0 (2 * Real.pi) :=
    (hcphase.mul (hcsin.pow 2)).intervalIntegrable _ _
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
      change (((Real.sin θ : ℝ) : ℂ) ^ 2) + (((Real.cos θ : ℝ) : ℂ) ^ 2) = 1
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
        · exact hcphase.intervalIntegrable _ _
        · exact (hcphase.mul ((hccos.pow 2).sub (hcsin.pow 2))).intervalIntegrable _ _
  have hfirstKernel :
      polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) := by
    simpa [polarFourierFirstCosineAngularKernel, cosine, phase, mul_comm] using hfirst
  calc
    2 * polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2)) := by
      rw [hfirstKernel]
      ring
    _ = _ := by rw [hsecond]

/-- The second cosine angular Fourier kernel is the normalized Bessel function
`-2π J₂`, for every real radial argument. -/
theorem polarFourierSecondCosineAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierSecondCosineAngularKernel z =
      -(((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 2 (z : ℂ)) := by
  by_cases hz : z = 0
  · subst z
    simp [Complex.besselJ_zero]
  · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
    have hK := polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second z
    rw [polarFourierFirstCosineAngularKernel_eq_besselJ,
      polarFourierZerothAngularKernel_eq_besselJ] at hK
    have hJ := besselJ_zero_one_two_recurrence (z : ℂ)
    apply mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hzc)
    linear_combination hK - (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * hJ

/-- The unnormalized first-harmonic recurrence also holds after finite radial
momentum integration. This reduces any weighted K1 moment to K0/K2 moments
with one additional radial power, without division by the Fourier argument,
a regulator limit, or any assumption on the weight. -/
theorem integral_polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
    (hbar pMax radius : ℝ) (f : ℝ → ℂ) :
    2 * (∫ p in (0 : ℝ)..pMax,
      (p : ℂ) *
        (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
      Complex.I * (((radius / hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p) := by
  calc
    2 * (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
        ∫ p in (0 : ℝ)..pMax,
          (2 : ℂ) * ((p : ℂ) *
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ p in (0 : ℝ)..pMax,
          (Complex.I * (((radius / hbar : ℝ) : ℂ))) *
            ((p : ℂ) ^ 2 *
              ((polarFourierZerothAngularKernel (p * radius / hbar) -
                  polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)) := by
      apply intervalIntegral.integral_congr
      intro p _
      have hrec :=
        polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
          (p * radius / hbar)
      have hp : ((p * radius / hbar : ℝ) : ℂ) =
          (p : ℂ) * (((radius / hbar : ℝ) : ℂ)) := by
        calc
          ((p * radius / hbar : ℝ) : ℂ) =
              ((p * (radius / hbar) : ℝ) : ℂ) := by
            congr 1
            ring
          _ = (p : ℂ) * (((radius / hbar : ℝ) : ℂ)) := by push_cast; rfl
      rw [hp] at hrec
      calc
        (2 : ℂ) * ((p : ℂ) *
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
          (p : ℂ) *
            (2 * polarFourierFirstCosineAngularKernel (p * radius / hbar)) * f p := by
            ring
        _ = (p : ℂ) *
            (Complex.I * ((p : ℂ) * (((radius / hbar : ℝ) : ℂ))) *
              (polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar))) * f p := by
            rw [hrec]
        _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Reflection across π makes the full-period integral of an antisymmetric
complex-valued integrand vanish. -/
private theorem integral_fullPeriod_eq_zero_of_reflection_neg
    (f : ℝ → ℂ) (hneg : ∀ θ, f (2 * Real.pi - θ) = -f θ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 := by
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hflip :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    simp_rw [hneg, intervalIntegral.integral_neg]
  exact CharZero.neg_eq_self_iff.mp (hflip.symm.trans hsub)

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- The mixed quadratic harmonic `cos θ sin θ` vanishes against the radial Fourier phase over one
full angle. -/
theorem integral_polarFourierRadialPhase_mul_cos_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ *
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- Phase-weighted full-angle integration of the canonical constant/first/second harmonic
decomposition. The first-sine and mixed-second channels vanish on the radial axis. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients
    (coefficients : AngularHarmonicCoefficients ℂ) (z p : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
        (p : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          polarFourierRadialPhase z θ * coefficients.eval θ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = _ := by
      congr 1
      simp only [AngularHarmonicCoefficients.eval, smul_eq_mul]
      simp_rw [mul_add, ← mul_assoc]
      repeat' rw [intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)]
      simp only [intervalIntegral.integral_mul_const]
      simp_rw [mul_assoc]
      simp only [integral_polarFourierRadialPhase_mul_sin_zero,
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
    integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

/-- The zeroth full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierZerothAngularKernel_neg (z : ℝ) :
    polarFourierZerothAngularKernel (-z) =
      polarFourierZerothAngularKernel z := by
  simp only [polarFourierZerothAngularKernel_eq_besselJ, Complex.ofReal_neg]
  congr 1
  simpa only [Int.cast_zero] using
    (Complex.even_besselJ (a := (0 : ℤ)) (by norm_num)) (z : ℂ)

/-- The first-cosine full-angle radial Fourier kernel is odd in its radial argument. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_neg (z : ℝ) :
    polarFourierFirstCosineAngularKernel (-z) =
      -polarFourierFirstCosineAngularKernel z := by
  have hodd : Complex.besselJ 1 (-(z : ℂ)) =
      -Complex.besselJ 1 (z : ℂ) := by
    simpa only [Int.cast_one] using
      (Complex.odd_besselJ (a := (1 : ℤ)) (by norm_num)) (z : ℂ)
  simp only [polarFourierFirstCosineAngularKernel_eq_besselJ, Complex.ofReal_neg,
    hodd]
  ring

/-- The second-cosine full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_neg (z : ℝ) :
    polarFourierSecondCosineAngularKernel (-z) =
      polarFourierSecondCosineAngularKernel z := by
  have heven : Complex.besselJ 2 (-(z : ℂ)) =
      Complex.besselJ 2 (z : ℂ) := by
    simpa using (Complex.even_besselJ (a := (2 : ℤ)) (by norm_num)) (z : ℂ)
  simp only [polarFourierSecondCosineAngularKernel_eq_besselJ, Complex.ofReal_neg,
    heven]

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
      simp_rw [polarFourierRadialPhase_conj]
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
      simp_rw [map_mul, Complex.conj_ofReal, polarFourierRadialPhase_conj]
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
      simp_rw [map_mul, map_sub, map_pow, Complex.conj_ofReal,
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

/-- Full-period integrals are unchanged by translating a periodic integrand.
This is also needed for Fourier harmonics at arbitrary polar angles. -/
private theorem intervalIntegral_fullPeriod_comp_sub_eq
    (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h := hf.intervalIntegral_add_eq (-angle) 0
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

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
        integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

/-- Phase-weighted full-angle reduction of canonical harmonic coefficients at an arbitrary
real-space polar angle. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients_shifted
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


end

end Transport
end QuantumTheory
