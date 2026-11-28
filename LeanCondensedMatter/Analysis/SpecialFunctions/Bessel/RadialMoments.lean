import LeanCondensedMatter.Analysis.ODE.RadialEnergyDecay
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.AnalyticWronskian

set_option linter.style.header false

/-!
# Radial Bessel moments and decay

Finite-interval Bessel-square integrals, radial first-order systems, and the
large-radius decay of the squared J₀/J₁ energy yield the J₁²/r radial moment.
The normalized real-axis Wronskian then reduces the Wronskian-weighted radial
moment to the same integral, with cutoff limit 1/π.

The Bessel differential and recurrence identities come from the hypergeometric series;
the Wronskian condition comes from the analytic Bessel theory. All limits here concern finite interval
integrals, independently of physical momentum normalization or regulators.
-/

namespace BesselRadialMoments

open BesselHypergeometric

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Exact derivative of the squared Bessel energy on the real axis. -/
private theorem besselEnergy_hasDerivAt (z : ℝ) :
    HasDerivAt (fun r : ℝ =>
      Complex.besselJ 0 (r : ℂ) ^ 2 + Complex.besselJ 1 (r : ℂ) ^ 2)
      (-2 * (Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ))) z := by
  have h := ((besselJ_zero_hasDerivAt (z : ℂ)).comp_ofReal.pow 2).add
    ((besselJ_one_hasDerivAt (z : ℂ)).comp_ofReal.pow 2)
  convert h using 1
  rw [besselJ_one_sq_div_eq_half_product]
  ring

/-- Exact finite-interval evaluation of the Bessel-square radial integral.
The recurrence gives a continuous extension of the quotient at the origin. -/
theorem integral_besselJ_one_sq_div (a b : ℝ) :
    (∫ z in a..b, Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ)) =
      ((Complex.besselJ 0 (a : ℂ) ^ 2 + Complex.besselJ 1 (a : ℂ) ^ 2) -
        (Complex.besselJ 0 (b : ℂ) ^ 2 + Complex.besselJ 1 (b : ℂ) ^ 2)) / 2 := by
  have h0 : Continuous (fun z : ℝ => Complex.besselJ 0 (z : ℂ)) :=
    continuous_iff_continuousAt.mpr fun z => (besselJ_zero_hasDerivAt (z : ℂ)).comp_ofReal.continuousAt
  have h1 : Continuous (fun z : ℝ => Complex.besselJ 1 (z : ℂ)) :=
    continuous_iff_continuousAt.mpr fun z => (besselJ_one_hasDerivAt (z : ℂ)).comp_ofReal.continuousAt
  have h2 : Continuous (fun z : ℝ => Complex.besselJ 2 (z : ℂ)) :=
    continuous_iff_continuousAt.mpr fun z => by
      simpa using (besselJ_nat_hasDerivAt 2 (z : ℂ)).comp_ofReal.continuousAt
  have hint : IntervalIntegrable (fun z : ℝ =>
      -2 * (Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ))) volume a b := by
    simp_rw [besselJ_one_sq_div_eq_half_product]
    exact (continuous_const.mul ((h1.mul (h0.add h2)).div_const 2)).intervalIntegrable a b
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => besselEnergy_hasDerivAt z) hint
  rw [intervalIntegral.integral_const_mul] at hftc
  linear_combination -hftc / 2

/-- The squared sum of the first two Bessel functions decays at infinity
by the radial first-order system and its Lyapunov bound. -/
theorem besselJ_zero_sq_add_one_sq_tendsto_zero :
    Filter.Tendsto (fun r : ℝ =>
      Complex.besselJ 0 (r : ℂ) ^ 2 +
        Complex.besselJ 1 (r : ℂ) ^ 2)
      Filter.atTop (nhds (0 : ℂ)) := by
  let X : ℝ → ℝ := fun r => (Complex.besselJ 0 (r : ℂ)).re
  let Y : ℝ → ℝ := fun r => (Complex.besselJ 1 (r : ℂ)).re
  have hXc (r : ℝ) : (X r : ℂ) = Complex.besselJ 0 (r : ℂ) := by
    simpa [X] using besselJ_nat_ofReal_re 0 r
  have hYc (r : ℝ) : (Y r : ℂ) = Complex.besselJ 1 (r : ℂ) := by
    simpa [Y] using besselJ_nat_ofReal_re 1 r
  have hX (r : ℝ) : HasDerivAt X (-Y r) r := by
    have h := (Complex.reCLM.hasFDerivAt.comp r
      (besselJ_zero_hasDerivAt (r : ℂ)).comp_ofReal.hasFDerivAt).hasDerivAt
    convert h using 1 <;> try rfl
    simp [Y]
  have hY (r : ℝ) (hr : r ≠ 0) : HasDerivAt Y (X r - Y r / r) r := by
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have hrec : 2 * Complex.besselJ 1 (r : ℂ) =
        (r : ℂ) * (Complex.besselJ 0 (r : ℂ) + Complex.besselJ 2 (r : ℂ)) := by
      simpa using besselJ_nat_recurrence 0 (r : ℂ)
    have hcoef : (Complex.besselJ 0 (r : ℂ) - Complex.besselJ 2 (r : ℂ)) / 2 =
        Complex.besselJ 0 (r : ℂ) - Complex.besselJ 1 (r : ℂ) / (r : ℂ) := by
      field_simp [hrc]
      linear_combination hrec
    have hc := (besselJ_one_hasDerivAt (r : ℂ)).comp_ofReal
    rw [hcoef] at hc
    have h := (Complex.reCLM.hasFDerivAt.comp r hc.hasFDerivAt).hasDerivAt
    convert h using 1 <;> try rfl
    have hre : X r - Y r / r =
        (Complex.besselJ 0 (r : ℂ) - Complex.besselJ 1 (r : ℂ) / (r : ℂ)).re := by
      rw [← hXc r, ← hYc r, ← Complex.ofReal_div, ← Complex.ofReal_sub]
      simp
    simpa [Complex.reCLM, ContinuousLinearMap.toSpanSingleton,
      ContinuousLinearMap.compSL] using hre
  have henergy : Filter.Tendsto (fun r : ℝ => X r ^ 2 + Y r ^ 2)
      Filter.atTop (nhds 0) := by
    apply RadialODE.energy_tendsto_zero_of_firstOrderSystem X Y
    · intro r _
      exact hX r
    · intro r hr
      exact hY r (by linarith)
  have hcast : Filter.Tendsto (fun r : ℝ =>
      ((X r ^ 2 + Y r ^ 2 : ℝ) : ℂ)) Filter.atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp henergy
  apply hcast.congr'
  exact Filter.Eventually.of_forall fun r => by
    push_cast
    rw [hXc r, hYc r]

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
