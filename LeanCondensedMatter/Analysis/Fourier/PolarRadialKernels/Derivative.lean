import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Differentiation of finite-cutoff radial Fourier integrals

The first-harmonic angular kernel is uniformly bounded by the angular
integration interval. This permits differentiation with respect to a signed
radial parameter through a **finite** radial integral for any
continuous complex radial weight. The interval endpoint and the Fourier scale are
arbitrary real parameters; no improper integral is differentiated.
-/

namespace PolarRadialKernels

noncomputable section

open MeasureTheory
open scoped Interval

/-- The zeroth full-angle Fourier harmonic has norm at most the
length `2π` of the angular interval, uniformly in the real argument.
This bound is used to control absolutely convergent spectral resolvent
*differences*, without any real-argument Bessel asymptotics. -/
theorem polarFourierZerothAngularKernel_norm_le (z : ℝ) :
    ‖polarFourierZerothAngularKernel z‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ => polarFourierRadialPhase z θ) (by
      intro θ _
      exact le_of_eq (norm_polarFourierRadialPhase z θ))
  simpa only [polarFourierZerothAngularKernel, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

/-- The first angular Fourier harmonic is uniformly bounded by the
length of the full angular interval, independently of its argument. -/
theorem polarFourierFirstCosineAngularKernel_norm_le (z : ℝ) :
    ‖polarFourierFirstCosineAngularKernel z‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ =>
      polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) (by
      intro θ _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_polarFourierRadialPhase, one_mul]
      exact Real.abs_cos_le_one θ)
  simpa only [polarFourierFirstCosineAngularKernel, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

/-- The finite-cutoff zeroth-harmonic integral is differentiable in the
real-space radius. The derivative is exactly its first cosine harmonic,
including the scale factor. In particular, this
theorem does not interchange a derivative with an improper integral. -/
theorem hasDerivAt_integral_polarFourierZerothAngularKernel
    (weight : ℝ → ℂ) (hweight : Continuous weight)
    (pMax scale radius : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ p in (0 : ℝ)..pMax,
        weight p * polarFourierZerothAngularKernel (p * r / scale))
      (∫ p in (0 : ℝ)..pMax,
        weight p * (Complex.I * ((p / scale : ℝ) : ℂ) *
          polarFourierFirstCosineAngularKernel (p * radius / scale)))
      radius := by
  let F : ℝ → ℝ → ℂ := fun r p =>
    weight p * polarFourierZerothAngularKernel (p * r / scale)
  let F' : ℝ → ℝ → ℂ := fun r p =>
    weight p * (Complex.I * ((p / scale : ℝ) : ℂ) *
      polarFourierFirstCosineAngularKernel (p * r / scale))
  let bound : ℝ → ℝ := fun p =>
    (‖weight p‖ * |p / scale|) * (2 * Real.pi)
  have hc0 : Continuous polarFourierZerothAngularKernel :=
    continuous_polarFourierZerothAngularKernel
  have hc1 : Continuous polarFourierFirstCosineAngularKernel :=
    continuous_polarFourierFirstCosineAngularKernel
  have hderiv (r p : ℝ) :
      HasDerivAt (fun t : ℝ => F t p) (F' r p) r := by
    have harg : HasDerivAt (fun t : ℝ => p * t / scale) (p / scale) r := by
      convert (((hasDerivAt_id r).const_mul p).div_const scale) using 1 <;>
        first | rfl | ring
    have hk := ((polarFourierZerothAngularKernel_hasDerivAt
      (p * r / scale)).hasFDerivAt.comp r harg.hasFDerivAt).hasDerivAt
    have h := hk.const_mul (weight p)
    convert h using 1
    · rfl
    · dsimp [F']
      push_cast
      ring
  have hcontArg (r : ℝ) : Continuous (fun p : ℝ => p * r / scale) := by
    fun_prop
  have hcontRatio : Continuous (fun p : ℝ => p / scale) := by
    fun_prop
  have hcont (r : ℝ) : Continuous (F r) := by
    dsimp [F]
    exact hweight.mul (hc0.comp (hcontArg r))
  have hcont' (r : ℝ) : Continuous (F' r) := by
    dsimp [F']
    exact hweight.mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp hcontRatio)).mul
        (hc1.comp (hcontArg r)))
  have hbound (r p : ℝ) : ‖F' r p‖ ≤ bound p := by
    have hn : ‖F' r p‖ =
        (‖weight p‖ * |p / scale|) *
          ‖polarFourierFirstCosineAngularKernel (p * r / scale)‖ := by
      dsimp [F']
      simp only [norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, one_mul]
      ring
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      (polarFourierFirstCosineAngularKernel_norm_le _) (by positivity)
  have hboundCont : Continuous bound := by
    dsimp [bound]
    exact (hweight.norm.mul hcontRatio.abs).mul continuous_const
  have hboundInt : IntervalIntegrable bound volume 0 pMax :=
    hboundCont.intervalIntegrable 0 pMax
  have hmain :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (s := Set.univ) (x₀ := radius) (a := (0 : ℝ)) (b := pMax)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun r => (hcont r).aestronglyMeasurable)
      ((hcont radius).intervalIntegrable _ _)
      ((hcont' radius).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p _ r _ => hbound r p)
      hboundInt
      (Filter.Eventually.of_forall fun p _ r _ => hderiv r p)).2
  change HasDerivAt
    (fun r : ℝ => ∫ p in (0 : ℝ)..pMax, F r p)
    (∫ p in (0 : ℝ)..pMax, F' radius p) radius
  exact hmain


/-- The second cosine harmonic is uniformly bounded on the real Fourier
axis. This also controls a second derivative of a finite radial Fourier
transform, without a Bessel asymptotic expansion. -/
theorem polarFourierSecondCosineAngularKernel_norm_le (z : ℝ) :
    ‖polarFourierSecondCosineAngularKernel z‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ =>
      polarFourierRadialPhase z θ *
        ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))) (by
      intro θ _
      have hreal : |Real.cos θ ^ 2 - Real.sin θ ^ 2| ≤ 1 := by
        apply abs_le.mpr
        constructor <;>
          nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ),
            sq_nonneg (Real.sin θ)]
      have hcast :
          (((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2) =
            ((Real.cos θ ^ 2 - Real.sin θ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, norm_polarFourierRadialPhase, one_mul, hcast,
        Complex.norm_real, Real.norm_eq_abs]
      exact hreal)
  simpa only [polarFourierSecondCosineAngularKernel, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

/-- A second finite-cutoff radial Fourier derivative. Unlike the first
derivative, the derivative of K1 contains *both* the isotropic K0 and
traceless K2 angular harmonics. No improper-integral differentiation or
nonzero-radius assumption is used. -/
theorem hasDerivAt_integral_polarFourierFirstCosineAngularKernel
    (weight : ℝ → ℂ) (hweight : Continuous weight)
    (pMax scale radius : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ p in (0 : ℝ)..pMax,
        weight p * polarFourierFirstCosineAngularKernel (p * r / scale))
      (∫ p in (0 : ℝ)..pMax,
        weight p * (((p / scale : ℝ) : ℂ) *
          ((Complex.I / 2) *
            (polarFourierZerothAngularKernel (p * radius / scale) +
              polarFourierSecondCosineAngularKernel (p * radius / scale)))))
      radius := by
  let F : ℝ → ℝ → ℂ := fun r p =>
    weight p * polarFourierFirstCosineAngularKernel (p * r / scale)
  let F' : ℝ → ℝ → ℂ := fun r p =>
    weight p * (((p / scale : ℝ) : ℂ) *
      ((Complex.I / 2) *
        (polarFourierZerothAngularKernel (p * r / scale) +
          polarFourierSecondCosineAngularKernel (p * r / scale))))
  let bound : ℝ → ℝ := fun p =>
    (‖weight p‖ * |p / scale|) * (3 * Real.pi)
  have hboundAngle (z : ℝ) :
      ‖(Complex.I / 2) *
          (polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z)‖ ≤ 3 * Real.pi := by
    calc
      _ = (1 / 2 : ℝ) *
          ‖polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z‖ := by
          simp [Complex.norm_I]
      _ ≤ (1 / 2 : ℝ) *
          (‖polarFourierZerothAngularKernel z‖ +
            ‖polarFourierSecondCosineAngularKernel z‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) * (2 * Real.pi + 2 * Real.pi) := by
          gcongr
          · exact polarFourierZerothAngularKernel_norm_le z
          · exact polarFourierSecondCosineAngularKernel_norm_le z
      _ ≤ 3 * Real.pi := by
          nlinarith [Real.pi_pos]
  have hderiv (r p : ℝ) :
      HasDerivAt (fun t : ℝ => F t p) (F' r p) r := by
    have harg : HasDerivAt (fun t : ℝ => p * t / scale) (p / scale) r := by
      convert (((hasDerivAt_id r).const_mul p).div_const scale) using 1 <;>
        first | rfl | ring
    have hk := ((polarFourierFirstCosineAngularKernel_hasDerivAt
      (p * r / scale)).hasFDerivAt.comp r harg.hasFDerivAt).hasDerivAt
    have h := hk.const_mul (weight p)
    convert h using 1
    · rfl
    · dsimp [F']
      push_cast
      ring
  have hc0 : Continuous polarFourierZerothAngularKernel :=
    continuous_polarFourierZerothAngularKernel
  have hc1 : Continuous polarFourierFirstCosineAngularKernel :=
    continuous_polarFourierFirstCosineAngularKernel
  have hc2 : Continuous polarFourierSecondCosineAngularKernel :=
    continuous_polarFourierSecondCosineAngularKernel
  have hcontArg (r : ℝ) : Continuous (fun p : ℝ => p * r / scale) := by
    fun_prop
  have hcontRatio : Continuous (fun p : ℝ => p / scale) := by fun_prop
  have hcont (r : ℝ) : Continuous (F r) := by
    dsimp [F]
    exact hweight.mul (hc1.comp (hcontArg r))
  have hcont' (r : ℝ) : Continuous (F' r) := by
    dsimp [F']
    exact hweight.mul
      ((Complex.continuous_ofReal.comp hcontRatio).mul
        (continuous_const.mul
          ((hc0.comp (hcontArg r)).add (hc2.comp (hcontArg r)))))
  have hbound (r p : ℝ) : ‖F' r p‖ ≤ bound p := by
    have hn : ‖F' r p‖ =
        (‖weight p‖ * |p / scale|) *
          ‖(Complex.I / 2) *
            (polarFourierZerothAngularKernel (p * r / scale) +
              polarFourierSecondCosineAngularKernel (p * r / scale))‖ := by
      dsimp [F']
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hboundAngle _) (by positivity)
  have hboundCont : Continuous bound := by
    dsimp [bound]
    exact (hweight.norm.mul hcontRatio.abs).mul continuous_const
  have hboundInt : IntervalIntegrable bound volume 0 pMax :=
    hboundCont.intervalIntegrable 0 pMax
  have hmain :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (s := Set.univ) (x₀ := radius) (a := (0 : ℝ)) (b := pMax)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun r => (hcont r).aestronglyMeasurable)
      ((hcont radius).intervalIntegrable _ _)
      ((hcont' radius).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p _ r _ => hbound r p)
      hboundInt
      (Filter.Eventually.of_forall fun p _ r _ => hderiv r p)).2
  change HasDerivAt
    (fun r : ℝ => ∫ p in (0 : ℝ)..pMax, F r p)
    (∫ p in (0 : ℝ)..pMax, F' radius p) radius
  exact hmain

end

end PolarRadialKernels
