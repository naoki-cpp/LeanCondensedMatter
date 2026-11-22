import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Differentiation of dimensionless polar Fourier kernels

Differentiate the zeroth and first-cosine full-angle kernels by a single
dominated-differentiation lemma for bounded continuous angular weights.
The resulting product rule gives the harmonic-energy derivative. Neither
the special-function representation nor physical momentum normalization
is needed.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Differentiate a polar Fourier angular integral with any continuous weight bounded by one.
The common domination estimate also covers higher bounded angular harmonics. -/
private theorem polarFourierWeightedAngularKernel_hasDerivAt
    (weight : ℝ → ℂ) (hweight : Continuous weight)
    (hbound : ∀ θ : ℝ, ‖weight θ‖ ≤ 1) (z : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        polarFourierRadialPhase x θ * weight θ)
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * weight θ) z := by
  let derivative : ℝ → ℝ → ℂ := fun x θ =>
    (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
      polarFourierRadialPhase x θ) * weight θ
  have hdiff (x θ : ℝ) :
      HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ * weight θ)
        (derivative x θ) x :=
    (polarFourierRadialPhase_hasDerivAt_radius x θ).mul_const (weight θ)
  have hcont (x : ℝ) : Continuous (fun θ : ℝ =>
      polarFourierRadialPhase x θ * weight θ) := by
    apply Continuous.mul
    · change Continuous (fun θ : ℝ =>
        Complex.exp (Complex.I * (((x * Real.cos θ : ℝ) : ℂ))))
      fun_prop
    · exact hweight
  have hcont' (x : ℝ) : Continuous (derivative x) := by
    dsimp only [derivative]
    apply Continuous.mul
    · change Continuous (fun θ : ℝ =>
        Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((x * Real.cos θ : ℝ) : ℂ))))
      fun_prop
    · exact hweight
  have hderivBound (x θ : ℝ) : ‖derivative x θ‖ ≤ (1 : ℝ) := by
    have hnorm : ‖derivative x θ‖ = |Real.cos θ| * ‖weight θ‖ := by
      simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, norm_polarFourierRadialPhase, one_mul, mul_one]
    rw [hnorm]
    calc
      |Real.cos θ| * ‖weight θ‖ ≤ 1 * ‖weight θ‖ :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _)
      _ = ‖weight θ‖ := one_mul _
      _ ≤ 1 := hbound θ
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => polarFourierRadialPhase x θ * weight θ)
    (F' := derivative)
    (bound := fun _θ : ℝ => (1 : ℝ))
    (s := Set.univ) (x₀ := z) (a := (0 : ℝ)) (b := 2 * Real.pi)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont z).intervalIntegrable _ _)
    ((hcont' z).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ _ x _ => hderivBound x θ)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => hdiff x θ)).2

/-- The first nonzero-argument differential relation of the radial Fourier
harmonics: the derivative of the zeroth angular kernel is `i` times the
first-cosine kernel.

Unlike an origin-only normalization, this holds for every real Fourier
argument. Together with the J₀ Bessel bridge and the hypergeometric-series
derivative, it yields the first-harmonic Bessel identity. -/
theorem polarFourierZerothAngularKernel_hasDerivAt (z : ℝ) :
    HasDerivAt polarFourierZerothAngularKernel
      (Complex.I * polarFourierFirstCosineAngularKernel z) z := by
  have h := polarFourierWeightedAngularKernel_hasDerivAt
    (fun _ : ℝ => (1 : ℂ)) continuous_const (by intro θ; simp) z
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * (1 : ℂ)) =
        Complex.I * polarFourierFirstCosineAngularKernel z := by
    unfold polarFourierFirstCosineAngularKernel
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hrew] at h
  change HasDerivAt
    (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase x θ)
    (Complex.I * polarFourierFirstCosineAngularKernel z) z
  simpa only [mul_one] using h

/-- Differentiating the first polar Fourier harmonic produces precisely the
isotropic plus second-harmonic channels. This is an all-real-argument
differential identity, not an origin-only or asymptotic statement. -/
theorem polarFourierFirstCosineAngularKernel_hasDerivAt (z : ℝ) :
    HasDerivAt polarFourierFirstCosineAngularKernel
      ((Complex.I / 2) *
        (polarFourierZerothAngularKernel z +
          polarFourierSecondCosineAngularKernel z)) z := by
  have h := polarFourierWeightedAngularKernel_hasDerivAt
    (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ))
    (by fun_prop)
    (by
      intro θ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ)
    z
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * ((Real.cos θ : ℝ) : ℂ)) =
        (Complex.I / 2) *
          (polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z) := by
    calc
      _ = (Complex.I / 2) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          polarFourierRadialPhase z θ +
            polarFourierRadialPhase z θ *
              (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro θ _
        have hs : (((Real.sin θ : ℝ) : ℂ) ^ 2) +
            (((Real.cos θ : ℝ) : ℂ) ^ 2) = 1 := by
          exact_mod_cast Real.sin_sq_add_cos_sq θ
        linear_combination (Complex.I / 2 * polarFourierRadialPhase z θ) * hs
      _ = _ := by
        rw [intervalIntegral.integral_add]
        · rfl
        · apply Continuous.intervalIntegrable
          unfold polarFourierRadialPhase
          fun_prop
        · apply Continuous.intervalIntegrable
          unfold polarFourierRadialPhase
          fun_prop
  rw [hrew] at h
  change HasDerivAt polarFourierFirstCosineAngularKernel
    ((Complex.I / 2) *
      (polarFourierZerothAngularKernel z +
        polarFourierSecondCosineAngularKernel z)) z at h
  exact h

/-- A finite-radius conservation-law primitive for the first two radial Fourier
harmonics. Its derivative involves the same K0-minus-K2 channel that occurs in
the Gaussian-crossed current moments; the identity is valid including z = 0. -/
theorem polarFourierHarmonicEnergy_hasDerivAt (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        polarFourierZerothAngularKernel t ^ 2 -
          polarFourierFirstCosineAngularKernel t ^ 2)
      (Complex.I * polarFourierFirstCosineAngularKernel z *
        (polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z)) z := by
  have h0 := (polarFourierZerothAngularKernel_hasDerivAt z).pow 2
  have h1 := (polarFourierFirstCosineAngularKernel_hasDerivAt z).pow 2
  convert h0.sub h1 using 1
  ring

end
end Transport
end QuantumTheory
