import LeanCondensedMatter.Transport.Analysis.PolarFourier
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

/-!
# Radial Bessel moments from the polar Fourier kernel

This module owns the analytic radial-moment calculations needed after polar
angular Fourier reduction: finite-interval Bessel-square integrals, the
radial first-order system, an elementary Lyapunov decay bound, and the
large-radius limit of the J₁²/r moment.

The upstream `PolarFourier` module retains the canonical angular kernels
and their differential/recurrence identities. This module does not alter
any physical momentum normalization, propagator, disorder approximation,
or regulator prescription. Its final theorem is a limit of finite interval
integrals, not an assertion about a regulated crossed diagram.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Exact finite-interval evaluation of the Bessel-square radial integral.
The formula holds for arbitrary real endpoints because J₁(0) = 0 gives the
continuous extension of the quotient at the origin. In particular, no
unproved Bessel asymptotic or improper-integral limit is used. -/
theorem integral_besselJ_one_sq_div (a b : ℝ) :
    (∫ z in a..b, Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) =
      ((Complex.besselJ 0 (a : ℂ) ^ 2 + Complex.besselJ 1 (a : ℂ) ^ 2) -
        (Complex.besselJ 0 (b : ℂ) ^ 2 + Complex.besselJ 1 (b : ℂ) ^ 2)) / 2 := by
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    have h : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    exact_mod_cast h
  have hbridge (z : ℝ) :
      polarFourierZerothAngularKernel z ^ 2 -
        polarFourierFirstCosineAngularKernel z ^ 2 =
      c ^ 2 *
        (Complex.besselJ 0 (z : ℂ) ^ 2 +
          Complex.besselJ 1 (z : ℂ) ^ 2) := by
    rw [polarFourierZerothAngularKernel_eq_besselJ,
      polarFourierFirstCosineAngularKernel_eq_besselJ]
    change (c * Complex.besselJ 0 (z : ℂ)) ^ 2 -
      (c * Complex.I * Complex.besselJ 1 (z : ℂ)) ^ 2 =
        c ^ 2 * (Complex.besselJ 0 (z : ℂ) ^ 2 +
          Complex.besselJ 1 (z : ℂ) ^ 2)
    calc
      _ = c ^ 2 * Complex.besselJ 0 (z : ℂ) ^ 2 -
          c ^ 2 * Complex.I ^ 2 * Complex.besselJ 1 (z : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hpoint (z : ℝ) :
      Complex.I * polarFourierFirstCosineAngularKernel z *
          (polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z) =
        (-2 * c ^ 2) * (Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) := by
    rw [polarFourierFirstCosineAngularKernel_eq_besselJ,
      polarFourierZerothAngularKernel_eq_besselJ,
      polarFourierSecondCosineAngularKernel_eq_besselJ,
      besselJ_one_sq_div_eq_half_product]
    change Complex.I * (c * Complex.I * Complex.besselJ 1 (z : ℂ)) *
        (c * Complex.besselJ 0 (z : ℂ) -
          -(c * Complex.besselJ 2 (z : ℂ))) =
      (-2 * c ^ 2) *
        (Complex.besselJ 1 (z : ℂ) *
          (Complex.besselJ 0 (z : ℂ) + Complex.besselJ 2 (z : ℂ)) / 2)
    calc
      _ = Complex.I ^ 2 * c ^ 2 * Complex.besselJ 1 (z : ℂ) *
          (Complex.besselJ 0 (z : ℂ) + Complex.besselJ 2 (z : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hLin :
      (∫ z in a..b,
        Complex.I * polarFourierFirstCosineAngularKernel z *
          (polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z)) =
        (-2 * c ^ 2) *
          (∫ z in a..b, Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _
    exact hpoint z
  have hftc := integral_polarFourierHarmonicEnergy a b
  rw [hLin, hbridge b, hbridge a] at hftc
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hfactor :
      c ^ 2 * (2 * (∫ z in a..b,
          Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) -
        ((Complex.besselJ 0 (a : ℂ) ^ 2 + Complex.besselJ 1 (a : ℂ) ^ 2) -
          (Complex.besselJ 0 (b : ℂ) ^ 2 + Complex.besselJ 1 (b : ℂ) ^ 2))) = 0 := by
    linear_combination -hftc
  have htwo :
      2 * (∫ z in a..b, Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) =
        (Complex.besselJ 0 (a : ℂ) ^ 2 + Complex.besselJ 1 (a : ℂ) ^ 2) -
          (Complex.besselJ 0 (b : ℂ) ^ 2 + Complex.besselJ 1 (b : ℂ) ^ 2) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hc2)
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  linear_combination htwo


/-- Real Cartesian channels of the canonical angular Fourier kernels. They
obey the same first-order system as the first two integer-order Bessel functions. -/
private noncomputable def polarFourierBesselX (r : ℝ) : ℝ :=
  (polarFourierZerothAngularKernel r).re

private noncomputable def polarFourierBesselY (r : ℝ) : ℝ :=
  (polarFourierFirstCosineAngularKernel r).im

private theorem polarFourierBesselX_hasDerivAt (r : ℝ) :
    HasDerivAt polarFourierBesselX (-polarFourierBesselY r) r := by
  have h := ((Complex.reCLM.hasFDerivAt.comp r
    (polarFourierZerothAngularKernel_hasDerivAt r).hasFDerivAt).hasDerivAt)
  convert h using 1
  · rfl
  · simp [polarFourierBesselY, Complex.mul_re]

private theorem polarFourierBesselY_hasDerivAt (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt polarFourierBesselY
      (polarFourierBesselX r - polarFourierBesselY r / r) r := by
  have h := ((Complex.imCLM.hasFDerivAt.comp r
    (polarFourierFirstCosineAngularKernel_hasDerivAt r).hasFDerivAt).hasDerivAt)
  have hangle := congrArg Complex.im
    (polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second r)
  have hs :
      ((Complex.I / 2) *
        (polarFourierZerothAngularKernel r +
          polarFourierSecondCosineAngularKernel r)).im =
        (polarFourierZerothAngularKernel r).re / 2 +
          (polarFourierSecondCosineAngularKernel r).re / 2 := by
    simp [Complex.mul_im, div_eq_mul_inv]
    ring
  have hrec :
      2 * polarFourierBesselY r =
        r * (polarFourierBesselX r -
          (polarFourierSecondCosineAngularKernel r).re) := by
    simpa [polarFourierBesselY, polarFourierBesselX,
      Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im] using hangle
  have hcoeff :
      (polarFourierZerothAngularKernel r).re / 2 +
        (polarFourierSecondCosineAngularKernel r).re / 2 =
      polarFourierBesselX r - polarFourierBesselY r / r := by
    dsimp [polarFourierBesselX] at hrec ⊢
    field_simp [hr]
    nlinarith [hrec]
  convert h using 1
  · rfl
  · simpa [Complex.imCLM, ContinuousLinearMap.toSpanSingleton,
      ContinuousLinearMap.compSL] using (hcoeff.symm.trans hs.symm)


/-- A quantitative Lyapunov argument for the radial Bessel first-order system.
The corrected energy `F = x² + y² - xy/r` obeys
`d/dr (r F²) = F (-x²-y²+3xy/r) ≤ 0` for `r ≥ 2`.
Consequently the energy tends to zero without invoking an asymptotic
Bessel expansion or assuming Fourier decay. -/
private theorem besselRadialSystem_energy_tendsto_zero
    (x y : ℝ → ℝ)
    (hx : ∀ r : ℝ, 2 ≤ r → HasDerivAt x (-y r) r)
    (hy : ∀ r : ℝ, 2 ≤ r → HasDerivAt y (x r - y r / r) r) :
    Filter.Tendsto (fun r : ℝ => x r ^ 2 + y r ^ 2)
      Filter.atTop (nhds 0) := by
  let E : ℝ → ℝ := fun r => x r ^ 2 + y r ^ 2
  let F : ℝ → ℝ := fun r => E r - x r * y r / r
  let H : ℝ → ℝ := fun r => r * F r ^ 2
  have hE_nonneg (r : ℝ) : 0 ≤ E r := by
    dsimp [E]
    positivity
  have hE_le_two_F (r : ℝ) (hr : 2 ≤ r) : E r ≤ 2 * F r := by
    have hxy : 2 * (x r * y r) ≤ E r := by
      dsimp [E]
      nlinarith [sq_nonneg (x r - y r)]
    have hrE : 0 ≤ (r - 1) * E r :=
      mul_nonneg (by linarith) (hE_nonneg r)
    have hxy' : 2 * (x r * y r) ≤ r * E r := by
      nlinarith [hxy, hrE]
    have hdiv : 2 * (x r * y r) / r ≤ E r :=
      (div_le_iff₀ (by linarith : 0 < r)).2 (by nlinarith [hxy'])
    have hrewrite : 2 * (x r * y r / r) = 2 * (x r * y r) / r := by ring
    rw [← hrewrite] at hdiv
    dsimp [F]
    linarith
  have hF_nonneg (r : ℝ) (hr : 2 ≤ r) : 0 ≤ F r := by
    linarith [hE_nonneg r, hE_le_two_F r hr]
  have hH_hasDerivAt (r : ℝ) (hr : 2 ≤ r) :
      HasDerivAt H
        (F r * (-E r + 3 * (x r * y r) / r)) r := by
    have hrne : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
    have hxr := hx r hr
    have hyr := hy r hr
    have hE' := (hxr.pow 2).add (hyr.pow 2)
    have hquot := (hxr.mul hyr).div (hasDerivAt_id r) hrne
    have hF' := hE'.sub hquot
    have hH' := (hasDerivAt_id r).mul (hF'.pow 2)
    convert hH' using 1
    · rfl
    · dsimp [E, F, H]
      field_simp [hrne]
      ring
  have hH_deriv_nonpos (r : ℝ) (hr : 2 ≤ r) :
      F r * (-E r + 3 * (x r * y r) / r) ≤ 0 := by
    have hxy : 2 * (x r * y r) ≤ E r := by
      dsimp [E]
      nlinarith [sq_nonneg (x r - y r)]
    have hrE : 0 ≤ (r - 2) * E r :=
      mul_nonneg (by linarith) (hE_nonneg r)
    have hxy' : 3 * (x r * y r) ≤ r * E r := by
      nlinarith [hxy, hrE, hE_nonneg r]
    have hdiv : 3 * (x r * y r) / r ≤ E r :=
      (div_le_iff₀ (by linarith : 0 < r)).2 (by nlinarith [hxy'])
    exact mul_nonpos_of_nonneg_of_nonpos (hF_nonneg r hr) (by linarith)
  have hanti : AntitoneOn H (Set.Ici (2 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (2 : ℝ))
    · intro r hr
      exact (hH_hasDerivAt r hr).continuousAt.continuousWithinAt
    · intro r hr
      have hr' : 2 ≤ r := by
        have hgt : 2 < r := by
          simpa only [interior_Ici, Set.mem_Ioi] using hr
        linarith
      exact (hH_hasDerivAt r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : 2 ≤ r := by
        have hgt : 2 < r := by
          simpa only [interior_Ici, Set.mem_Ioi] using hr
        linarith
      rw [(hH_hasDerivAt r hr').deriv]
      exact hH_deriv_nonpos r hr'
  have hSqBound (r : ℝ) (hr : 2 ≤ r) :
      F r ^ 2 ≤ H 2 / r := by
    have hupper := hanti (show (2 : ℝ) ∈ Set.Ici 2 by norm_num)
      (Set.mem_Ici.mpr hr) hr
    apply (le_div_iff₀ (by linarith : 0 < r)).2
    simpa only [H, mul_comm] using hupper
  have hUpperLim :
      Filter.Tendsto (fun r : ℝ => H 2 / r) Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
        Filter.atTop Filter.atTop).const_div_atTop (H 2)
  have hSqLim : Filter.Tendsto (fun r : ℝ => F r ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact sq_nonneg (F r)
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hSqBound r hr
    · exact hUpperLim
  have hFLim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have hroot : Filter.Tendsto (fun r : ℝ => Real.sqrt (F r ^ 2))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hSqLim
    apply hroot.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hF_nonneg r hr)]
  have hDouble : Filter.Tendsto (fun r : ℝ => 2 * F r)
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hFLim) using 1
    norm_num
  have hELim : Filter.Tendsto E Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hE_nonneg r
    · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with r hr
      exact hE_le_two_F r hr
    · exact hDouble
  exact hELim


/-- The real scalar/vector channels of the exact radial Fourier kernel decay
jointly, by the Lyapunov bound for their proved first-order radial system. -/
private theorem polarFourierBesselEnergy_tendsto_zero :
    Filter.Tendsto (fun r : ℝ =>
      polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2)
      Filter.atTop (nhds 0) := by
  apply besselRadialSystem_energy_tendsto_zero
    polarFourierBesselX polarFourierBesselY
  · intro r _
    exact polarFourierBesselX_hasDerivAt r
  · intro r hr
    exact polarFourierBesselY_hasDerivAt r (by linarith)


/-- The zeroth Fourier harmonic is real, and equals the real embedding of its
radial Lyapunov-system coordinate. -/
private theorem polarFourierZerothAngularKernel_eq_ofReal_re (r : ℝ) :
    polarFourierZerothAngularKernel r = (polarFourierBesselX r : ℂ) := by
  have him : (polarFourierZerothAngularKernel r).im = 0 := by
    have h := congrArg Complex.im (polarFourierZerothAngularKernel_conj r)
    simp only [Complex.conj_im] at h
    linarith
  apply Complex.ext
  · simp [polarFourierBesselX]
  · simpa using him

/-- The first-cosine Fourier harmonic is purely imaginary, with imaginary
coordinate given by the other component of the Lyapunov system. -/
private theorem polarFourierFirstCosineAngularKernel_eq_I_ofReal_im (r : ℝ) :
    polarFourierFirstCosineAngularKernel r =
      Complex.I * (polarFourierBesselY r : ℂ) := by
  have hre : (polarFourierFirstCosineAngularKernel r).re = 0 := by
    have h := congrArg Complex.re (polarFourierFirstCosineAngularKernel_conj r)
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  apply Complex.ext
  · simp [Complex.mul_re, hre]
  · simp [Complex.mul_im, polarFourierBesselY]

/-- The squared Fourier harmonics have a vanishing limit at large positive
radius. This is a consequence of the explicit radial ODE energy bound, not a
postulated Bessel-function asymptotic. -/
theorem polarFourierHarmonicEnergy_tendsto_zero :
    Filter.Tendsto (fun r : ℝ =>
      polarFourierZerothAngularKernel r ^ 2 -
        polarFourierFirstCosineAngularKernel r ^ 2)
      Filter.atTop (nhds (0 : ℂ)) := by
  have hcast : Filter.Tendsto (fun r : ℝ =>
      ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp
        polarFourierBesselEnergy_tendsto_zero
  apply hcast.congr'
  exact Filter.Eventually.of_forall fun r => by
    change ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ) =
      polarFourierZerothAngularKernel r ^ 2 -
        polarFourierFirstCosineAngularKernel r ^ 2
    rw [polarFourierZerothAngularKernel_eq_ofReal_re,
      polarFourierFirstCosineAngularKernel_eq_I_ofReal_im]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring

/-- The squared sum of the canonical integer-order Bessel functions decays
at infinity, following from the proved Fourier--Bessel identities and
the Lyapunov bound. -/
theorem besselJ_zero_sq_add_one_sq_tendsto_zero :
    Filter.Tendsto (fun r : ℝ =>
      Complex.besselJ 0 (r : ℂ) ^ 2 +
        Complex.besselJ 1 (r : ℂ) ^ 2)
      Filter.atTop (nhds (0 : ℂ)) := by
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    have hr : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    exact_mod_cast hr
  have hbridge (r : ℝ) :
      polarFourierZerothAngularKernel r ^ 2 -
        polarFourierFirstCosineAngularKernel r ^ 2 =
      c ^ 2 * (Complex.besselJ 0 (r : ℂ) ^ 2 +
        Complex.besselJ 1 (r : ℂ) ^ 2) := by
    rw [polarFourierZerothAngularKernel_eq_besselJ,
      polarFourierFirstCosineAngularKernel_eq_besselJ]
    change (c * Complex.besselJ 0 (r : ℂ)) ^ 2 -
      (c * Complex.I * Complex.besselJ 1 (r : ℂ)) ^ 2 =
        c ^ 2 * (Complex.besselJ 0 (r : ℂ) ^ 2 +
          Complex.besselJ 1 (r : ℂ) ^ 2)
    calc
      _ = c ^ 2 * Complex.besselJ 0 (r : ℂ) ^ 2 -
          c ^ 2 * Complex.I ^ 2 * Complex.besselJ 1 (r : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hscaled : Filter.Tendsto (fun r : ℝ =>
      (c ^ 2)⁻¹ * (polarFourierZerothAngularKernel r ^ 2 -
        polarFourierFirstCosineAngularKernel r ^ 2))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [mul_zero] using
      (polarFourierHarmonicEnergy_tendsto_zero.const_mul (c ^ 2)⁻¹)
  apply hscaled.congr'
  exact Filter.Eventually.of_forall fun r => by
    change (c ^ 2)⁻¹ *
      (polarFourierZerothAngularKernel r ^ 2 -
        polarFourierFirstCosineAngularKernel r ^ 2) =
      Complex.besselJ 0 (r : ℂ) ^ 2 + Complex.besselJ 1 (r : ℂ) ^ 2
    rw [hbridge r]
    field_simp [pow_ne_zero 2 hc]

/-- The large-cutoff limit of the finite-interval first-order Bessel radial
moment is exactly one half. The result is stated as a limit of finite
interval integrals, without conflating it with an unproved Bochner
integrability statement on an infinite set. -/
theorem tendsto_integral_besselJ_one_sq_div :
    Filter.Tendsto (fun R : ℝ =>
      ∫ r in (0 : ℝ)..R, Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ))
      Filter.atTop (nhds (1 / 2 : ℂ)) := by
  have hpoint (R : ℝ) :
      (∫ r in (0 : ℝ)..R, Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) =
        (1 - (Complex.besselJ 0 (R : ℂ) ^ 2 +
          Complex.besselJ 1 (R : ℂ) ^ 2)) / 2 := by
    rw [integral_besselJ_one_sq_div 0 R]
    simp [Complex.besselJ_zero]
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℂ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have hlimit := (hconst.sub besselJ_zero_sq_add_one_sq_tendsto_zero).div_const
    (2 : ℂ)
  convert hlimit using 1
  · funext R
    exact hpoint R
  · norm_num

end

end Transport
end QuantumTheory
