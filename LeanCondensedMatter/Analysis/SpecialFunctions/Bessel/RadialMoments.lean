import LeanCondensedMatter.Analysis.ODE.RadialEnergyDecay
import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

/-!
# Radial Bessel moments and Fourier–Bessel decay

This mathematical module proves radial-moment identities using the angular
Fourier–Bessel kernels in Analysis: finite-interval Bessel-square integrals, the
radial first-order system, an elementary Lyapunov decay bound, and the
large-radius limit of the J₁²/r moment.

The upstream `Analysis.Fourier.PolarRadialKernels` module owns the canonical angular
kernels and their differential/recurrence identities. This module does not alter
any physical momentum normalization, propagator, disorder approximation,
or regulator prescription. Its final theorem is a limit of finite interval
integrals, not an assertion about a regulated crossed diagram.
-/

namespace BesselRadialMoments

open QuantumTheory.Transport

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- The first-harmonic radial product has an exact finite-interval primitive.
This is the finite-radius endpoint identity needed before an improper
Bessel-square integral and its regulator limits can be established. -/
theorem integral_polarFourierHarmonicEnergy (a b : ℝ) :
    (∫ z in a..b,
      Complex.I * polarFourierFirstCosineAngularKernel z *
        (polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z)) =
      (polarFourierZerothAngularKernel b ^ 2 -
        polarFourierFirstCosineAngularKernel b ^ 2) -
      (polarFourierZerothAngularKernel a ^ 2 -
        polarFourierFirstCosineAngularKernel a ^ 2) := by
  have hc0 : Continuous polarFourierZerothAngularKernel :=
    continuous_iff_continuousAt.mpr fun z =>
      (polarFourierZerothAngularKernel_hasDerivAt z).continuousAt
  have hc1 : Continuous polarFourierFirstCosineAngularKernel :=
    continuous_iff_continuousAt.mpr fun z =>
      (polarFourierFirstCosineAngularKernel_hasDerivAt z).continuousAt
  have hJ2 : Continuous (fun z : ℝ => Complex.besselJ 2 (z : ℂ)) := by
    have h : Continuous (Complex.besselJ (2 : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro w
      simpa using (Complex.analyticAt_besselJ_int (2 : ℤ) w).continuousAt
    exact h.comp Complex.continuous_ofReal
  have hc2 : Continuous polarFourierSecondCosineAngularKernel := by
    have hfun : polarFourierSecondCosineAngularKernel =
        fun z : ℝ =>
          -(((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 2 (z : ℂ)) := by
      funext z
      exact polarFourierSecondCosineAngularKernel_eq_besselJ z
    rw [hfun]
    exact (continuous_const.mul hJ2).neg
  have hint : IntervalIntegrable (fun z : ℝ =>
      Complex.I * polarFourierFirstCosineAngularKernel z *
        (polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z)) volume a b :=
    ((continuous_const.mul hc1).mul (hc0.sub hc2)).intervalIntegrable a b
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => polarFourierHarmonicEnergy_hasDerivAt z) hint

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


/-- The real scalar/vector channels of the exact radial Fourier kernel decay
jointly, by the Lyapunov bound for their proved first-order radial system. -/
private theorem polarFourierBesselEnergy_tendsto_zero :
    Filter.Tendsto (fun r : ℝ =>
      polarFourierBesselX r ^ 2 + polarFourierBesselY r ^ 2)
      Filter.atTop (nhds 0) := by
  apply RadialODE.energy_tendsto_zero_of_firstOrderSystem
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
    simpa only [c] using polarFourierHarmonicEnergy_eq_besselJ r
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

end BesselRadialMoments
