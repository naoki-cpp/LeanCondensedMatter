import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.ZerothBessel
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Differentiation
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Higher polar Fourier harmonics and symmetry

First- and second-order Fourier–Bessel identities, the integration-by-parts
recurrence, weighted radial moments, and parity/conjugation laws. This
pure analysis layer has no physical-momentum normalization.
-/

namespace QuantumTheory
open BesselHypergeometric
namespace Transport

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
        (-Complex.I) * (Complex.I * polarFourierFirstCosineAngularKernel z) := by
      rw [← mul_assoc, hI, one_mul]
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
  have hzero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ +
          sine θ * ((-Complex.I * (z : ℂ) * sine θ) * phase θ)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := sine) (v := phase) (u' := cosine)
      (v' := fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ)
      (fun θ _ => by
        simpa [sine, cosine] using (Real.hasDerivAt_sin θ).ofReal_comp)
      (fun θ _ => polarFourierRadialPhase_hasDerivAt z θ)
      (hccos.intervalIntegrable _ _)
      (((continuous_const.mul hcsin).mul hcphase).intervalIntegrable _ _)
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
    change 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ) -
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          phase θ * (cosine θ ^ 2 - sine θ ^ 2))
    rw [← intervalIntegral.integral_const_mul]
    calc
      _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
          phase θ - phase θ * (cosine θ ^ 2 - sine θ ^ 2) :=
        intervalIntegral.integral_congr (fun θ _ => htrig θ)
      _ = _ :=
        intervalIntegral.integral_sub
          (hcphase.intervalIntegrable _ _)
          ((hcphase.mul ((hccos.pow 2).sub (hcsin.pow 2))).intervalIntegrable _ _)
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

end
end Transport
end QuantumTheory
