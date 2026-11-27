import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option linter.style.header false

/-!
# Dimensionless polar Fourier kernels: definitions, derivatives and angular reduction

The phase `exp(i z cos θ)` and the zeroth, first-cosine, and second-cosine
full-angle kernels. This independent base layer provides elementary values at
the origin and continuity, without a Bessel-function representation, Fourier
momentum measure, or transport assumption.
-/

namespace PolarRadialKernels

open AngularHarmonics

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- Zeroth full-angle radial Fourier kernel, identified with `2π J₀(z)` by
`polarFourierZerothAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel, identified with `2π i J₁(z)`
by `polarFourierFirstCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)`
polynomial for quadratic angular products and identified with `-2π J₂(z)`
by `polarFourierSecondCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

/-- The Fourier phase has unit norm for every real argument. -/
theorem norm_polarFourierRadialPhase (z θ : ℝ) :
    ‖polarFourierRadialPhase z θ‖ = 1 := by
  simp [polarFourierRadialPhase, Complex.norm_exp, Complex.mul_re]

/-- Derivative of the dimensionless radial Fourier phase with respect to the polar angle. -/
theorem polarFourierRadialPhase_hasDerivAt (z θ : ℝ) :
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
  · simp [polarFourierRadialPhase]
    ring

/-- Derivative of the dimensionless Fourier phase with respect to its radial argument. -/
theorem polarFourierRadialPhase_hasDerivAt_radius (z θ : ℝ) :
    HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ)
      (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
        polarFourierRadialPhase z θ) z := by
  have hmul : HasDerivAt (fun t : ℝ => t * Real.cos θ)
      (Real.cos θ) z := by
    simpa using (hasDerivAt_id z).mul_const (Real.cos θ)
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
      (Complex.I * ((Real.cos θ : ℝ) : ℂ)) z :=
    hmul.ofReal_comp |>.const_mul Complex.I
  have hphase := (Complex.hasDerivAt_exp _).comp z harg
  convert hphase using 1
  · rfl
  · dsimp [polarFourierRadialPhase]
    ring

/-- Complex conjugation of the angular Fourier phase reverses its radial argument. -/
theorem polarFourierRadialPhase_conj (z θ : ℝ) :
    conj (polarFourierRadialPhase z θ) =
      polarFourierRadialPhase (-z) θ := by
  unfold polarFourierRadialPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The zeroth radial Fourier kernel is normalized by the full polar angle at the origin. -/
@[simp] theorem polarFourierZerothAngularKernel_zero :
    polarFourierZerothAngularKernel 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [polarFourierZerothAngularKernel, polarFourierRadialPhase]

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using
    (integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi))

/-- The second-cosine angular Fourier kernel vanishes at zero radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_zero :
    polarFourierSecondCosineAngularKernel 0 = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 1
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval,
    polarFourierSecondCosineAngularKernel, polarFourierRadialPhase,
    smul_eq_mul] using coefficients.integral_eval

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


end
end PolarRadialKernels

/-!
## Differentiation of dimensionless polar Fourier kernels

Differentiate the zeroth and first-cosine full-angle kernels by a single
dominated-differentiation lemma for bounded continuous angular weights.
The resulting product rule gives the harmonic-energy derivative. Neither
the special-function representation nor physical momentum normalization
is needed.
-/

namespace PolarRadialKernels

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
  have hcos : Continuous (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ)) := by
    fun_prop
  have hphase (x : ℝ) : Continuous (polarFourierRadialPhase x) := by
    unfold polarFourierRadialPhase
    fun_prop
  have hcont (x : ℝ) : Continuous (fun θ : ℝ =>
      polarFourierRadialPhase x θ * weight θ) :=
    (hphase x).mul hweight
  have hcont' (x : ℝ) : Continuous (derivative x) :=
    (((continuous_const.mul hcos).mul (hphase x)).mul hweight)
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
end PolarRadialKernels

/-!
## Polar Fourier angular harmonic reductions

Reduction of constant, first and second angular harmonics against the
radial Fourier phase, together with reflection cancellations and arbitrary
polar-angle shifts. This layer depends only on the core kernels and
model-independent harmonic coefficients.
-/

namespace PolarRadialKernels
open AngularHarmonics

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

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
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
      rw [intervalIntegral.integral_comp_sub_right]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hf.intervalIntegral_add_eq (-angle) 0
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
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
      have hchange :
          (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
            ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
              ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [f, coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul]
        rw [Real.cos_add, Real.sin_add]
        push_cast
        ring
      rw [hchange]
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
end PolarRadialKernels
