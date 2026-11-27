import LeanCondensedMatter.Analysis.ODE.RadialEnergyDecay
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Bessel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.AnalyticWronskian

set_option linter.style.header false

/-!
# Radial Bessel moments and Fourier–Bessel decay

Finite-interval Bessel-square integrals, radial first-order systems, and the
large-radius decay of the squared J₀/J₁ energy yield the J₁²/r radial moment.
The normalized real-axis Wronskian then reduces the Wronskian-weighted radial
moment to the same integral, with cutoff limit 1/π.

The angular Fourier kernels and their differential identities come from
`Analysis.Fourier.PolarRadialKernels.Bessel`; the Wronskian condition
comes from the analytic Bessel theory. All limits here concern finite interval
integrals, independently of physical momentum normalization or regulators.
-/

namespace BesselRadialMoments

open PolarRadialKernels

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- The Fourier normalization of the squared J₀/J₁ energy, shared by the
finite-interval moment and its large-radius limit. -/
private theorem polarFourierHarmonicEnergy_eq_besselJ (r : ℝ) :
    polarFourierZerothAngularKernel r ^ 2 -
      polarFourierFirstCosineAngularKernel r ^ 2 =
      (((2 * Real.pi : ℝ) : ℂ) ^ 2) *
        (Complex.besselJ 0 (r : ℂ) ^ 2 +
          Complex.besselJ 1 (r : ℂ) ^ 2) := by
  rw [polarFourierZerothAngularKernel_eq_besselJ,
    polarFourierFirstCosineAngularKernel_eq_besselJ]
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ) ^ 2) *
        (Complex.besselJ 0 (r : ℂ) ^ 2 -
          Complex.I ^ 2 * Complex.besselJ 1 (r : ℂ) ^ 2) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

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
    simpa only [c] using polarFourierHarmonicEnergy_eq_besselJ z
  have hpoint (z : ℝ) :
      Complex.I * polarFourierFirstCosineAngularKernel z *
          (polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z) =
        (-2 * c ^ 2) * (Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) := by
    rw [polarFourierFirstCosineAngularKernel_eq_besselJ,
      polarFourierZerothAngularKernel_eq_besselJ,
      polarFourierSecondCosineAngularKernel_eq_besselJ,
      BesselHypergeometric.besselJ_one_sq_div_eq_half_product]
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
  have hftc :
    (∫ z in a..b,
      Complex.I * polarFourierFirstCosineAngularKernel z *
        (polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z)) =
      (polarFourierZerothAngularKernel b ^ 2 -
        polarFourierFirstCosineAngularKernel b ^ 2) -
      (polarFourierZerothAngularKernel a ^ 2 -
        polarFourierFirstCosineAngularKernel a ^ 2) := by
    have hint : IntervalIntegrable (fun z : ℝ =>
        Complex.I * polarFourierFirstCosineAngularKernel z *
          (polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z)) volume a b :=
      ((continuous_const.mul continuous_polarFourierFirstCosineAngularKernel).mul
        (continuous_polarFourierZerothAngularKernel.sub
          continuous_polarFourierSecondCosineAngularKernel)).intervalIntegrable a b
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => polarFourierHarmonicEnergy_hasDerivAt z) hint
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
    simpa only [c] using polarFourierHarmonicEnergy_eq_besselJ r
  have henergy : Filter.Tendsto (fun r : ℝ =>
      polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2)
      Filter.atTop (nhds 0) := by
    apply RadialODE.energy_tendsto_zero_of_firstOrderSystem
      polarFourierBesselX polarFourierBesselY
    · intro r _
      exact polarFourierBesselX_hasDerivAt r
    · intro r hr
      exact polarFourierBesselY_hasDerivAt r (by linarith)
  have hcast : Filter.Tendsto (fun r : ℝ =>
      ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp henergy
  have hscaled : Filter.Tendsto (fun r : ℝ =>
      (c ^ 2)⁻¹ *
        ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [mul_zero] using hcast.const_mul (c ^ 2)⁻¹
  apply hscaled.congr'
  exact Filter.Eventually.of_forall fun r => by
    change (c ^ 2)⁻¹ *
      ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ) =
      Complex.besselJ 0 (r : ℂ) ^ 2 + Complex.besselJ 1 (r : ℂ) ^ 2
    have hkernel :
        ((polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2 : ℝ) : ℂ) =
          polarFourierZerothAngularKernel r ^ 2 -
            polarFourierFirstCosineAngularKernel r ^ 2 := by
      rw [polarFourierZerothAngularKernel_eq_ofReal_re,
        polarFourierFirstCosineAngularKernel_eq_I_ofReal_im]
      push_cast
      rw [mul_pow, Complex.I_sq]
      ring
    rw [hkernel, hbridge r]
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

end BesselRadialMoments

/-! ## Wronskian-weighted radial moments -/

namespace BesselRadialMoments

open BesselSecondKind

noncomputable section

open MeasureTheory
open scoped Interval

/-- The finite-radius Gaussian Wronskian-weighted Bessel integral is an explicit
endpoint expression, under only the standard Wronskian condition.
The Y functions never need values or continuity at r=0. -/
theorem integral_wronskianBesselIntegrand_eq_endpoints
    (Y0 Y1 : ℝ → ℂ) (hW : RealWronskianCondition Y0 Y1)
    (R : ℝ) :
    (∫ r in (0 : ℝ)..R,
        Complex.besselJ 1 (r : ℂ) ^ 2 *
          (Complex.besselJ 1 (r : ℂ) * Y0 r -
            Complex.besselJ 0 (r : ℂ) * Y1 r)) =
      (((2 / Real.pi : ℝ) : ℂ)) *
        ((1 - (Complex.besselJ 0 (R : ℂ) ^ 2 +
            Complex.besselJ 1 (R : ℂ) ^ 2)) / 2) := by
  calc
    _ = (∫ r in (0 : ℝ)..R,
          (((2 / Real.pi : ℝ) : ℂ)) *
            (Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ))) := by
        apply intervalIntegral.integral_congr
        intro r _
        change Complex.besselJ 1 (r : ℂ) ^ 2 *
            (Complex.besselJ 1 (r : ℂ) * Y0 r -
              Complex.besselJ 0 (r : ℂ) * Y1 r) =
          (((2 / Real.pi : ℝ) : ℂ)) *
            (Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ))
        by_cases hr : r = 0
        · subst r
          simp [Complex.besselJ_zero]
        · rw [hW r hr]
          ring
    _ = (((2 / Real.pi : ℝ) : ℂ)) *
          (∫ r in (0 : ℝ)..R,
            Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = _ := by
        rw [integral_besselJ_one_sq_div]
        simp [Complex.besselJ_zero]

/-- The Wronskian-weighted Bessel radial integral has universal cutoff
limit `1/π` for any pair of functions satisfying the normalized real-axis
Wronskian. This proves a special-function identity, not a physical
disorder or crossed-diagram limit. -/
theorem tendsto_integral_wronskianBesselIntegrand_one_div_pi
    (Y0 Y1 : ℝ → ℂ) (hW : RealWronskianCondition Y0 Y1) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        Complex.besselJ 1 (r : ℂ) ^ 2 *
          (Complex.besselJ 1 (r : ℂ) * Y0 r -
            Complex.besselJ 0 (r : ℂ) * Y1 r))
      Filter.atTop (nhds (((1 / Real.pi : ℝ) : ℂ))) := by
  have hlimit := (tendsto_integral_besselJ_one_sq_div).const_mul
    (((2 / Real.pi : ℝ) : ℂ))
  have hpoint (R : ℝ) :
      (((2 / Real.pi : ℝ) : ℂ)) *
          (∫ r in (0 : ℝ)..R,
            Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) =
        ∫ r in (0 : ℝ)..R,
          Complex.besselJ 1 (r : ℂ) ^ 2 *
            (Complex.besselJ 1 (r : ℂ) * Y0 r -
              Complex.besselJ 0 (r : ℂ) * Y1 r) := by
    rw [integral_besselJ_one_sq_div]
    simpa [Complex.besselJ_zero] using
      (integral_wronskianBesselIntegrand_eq_endpoints Y0 Y1 hW R).symm
  have hscale : (((2 / Real.pi : ℝ) : ℂ)) * (1 / 2 : ℂ) =
      ((1 / Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [hscale] using
    hlimit.congr' (Filter.Eventually.of_forall hpoint)


end

end BesselRadialMoments
