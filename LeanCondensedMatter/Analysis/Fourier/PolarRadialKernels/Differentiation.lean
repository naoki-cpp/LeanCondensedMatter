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
        (derivative x θ) x := by
    have hmul : HasDerivAt (fun t : ℝ => t * Real.cos θ)
        (Real.cos θ) x := by
      simpa using (hasDerivAt_id x).mul_const (Real.cos θ)
    have harg : HasDerivAt
        (fun t : ℝ => Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
        (Complex.I * ((Real.cos θ : ℝ) : ℂ)) x :=
      hmul.ofReal_comp |>.const_mul Complex.I
    have hphase := (Complex.hasDerivAt_exp _).comp x harg
    have hbase : HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ)
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase x θ) x := by
      convert hphase using 1
      · rfl
      · dsimp [polarFourierRadialPhase]
        ring
    exact hbase.mul_const (weight θ)
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
  let derivative : ℝ → ℝ → ℂ := fun x θ =>
    Complex.I * ((((Real.cos θ : ℝ) : ℂ)) ^ 2) * polarFourierRadialPhase x θ
  have h := polarFourierWeightedAngularKernel_hasDerivAt
    (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ))
    (by fun_prop)
    (by
      intro θ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ)
    z
  have hderiv :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * ((Real.cos θ : ℝ) : ℂ)) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [derivative]
    ring
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) =
        (Complex.I / 2) *
          (polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z) := by
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (Complex.I / 2) *
              (polarFourierRadialPhase z θ +
                polarFourierRadialPhase z θ *
                  (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                    ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro θ _
        have hs : (((Real.sin θ : ℝ) : ℂ) ^ 2) +
            (((Real.cos θ : ℝ) : ℂ) ^ 2) = 1 := by
          exact_mod_cast Real.sin_sq_add_cos_sq θ
        dsimp [derivative]
        linear_combination (Complex.I / 2 * polarFourierRadialPhase z θ) * hs
      _ = (Complex.I / 2) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            polarFourierRadialPhase z θ +
              polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add]
        · rfl
        · have hc : Continuous (polarFourierRadialPhase z) := by
            change Continuous (fun θ : ℝ =>
              Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))))
            fun_prop
          exact hc.intervalIntegrable _ _
        · have hc : Continuous (fun θ : ℝ =>
              polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
            change Continuous (fun θ : ℝ =>
              Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2))
            fun_prop
          exact hc.intervalIntegrable _ _
  rw [hderiv, hrew] at h
  change HasDerivAt
    (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase x θ * ((Real.cos θ : ℝ) : ℂ))
    ((Complex.I / 2) *
      (polarFourierZerothAngularKernel z +
        polarFourierSecondCosineAngularKernel z)) z
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
