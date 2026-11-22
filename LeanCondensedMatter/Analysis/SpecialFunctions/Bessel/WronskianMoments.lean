import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.RadialMoments
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.AnalyticWronskian

set_option linter.style.header false

/-!
# Wronskian-weighted Bessel radial moments

The scalar radial integrand is

  J₁(r)² (J₁(r) Y₀(r) - J₀(r) Y₁(r)).

For functions satisfying `BesselSecondKind.RealWronskianCondition`,
the Wronskian reduces the integrand to `(2/π) J₁(r)²/r`, including
the origin by the natural zero extension. The finite interval integral
has an exact endpoint expression and its cutoff limit is `1/π`.

These are special-function identities independent of any transport
model, physical cutoff, disorder approximation, or conductivity claim.
-/

namespace BesselRadialMoments

open BesselSecondKind

noncomputable section

open MeasureTheory
open scoped Interval

/-- Exact Wronskian reduction of the X radial integrand, including the
origin via the continuous J₁²/r extension. -/
theorem wronskianBesselIntegrand_eq_one_sq_div
    (Y0 Y1 : ℝ → ℂ) (hW : RealWronskianCondition Y0 Y1)
    (r : ℝ) :
    Complex.besselJ 1 (r : ℂ) ^ 2 *
        (Complex.besselJ 1 (r : ℂ) * Y0 r -
          Complex.besselJ 0 (r : ℂ) * Y1 r) =
      (((2 / Real.pi : ℝ) : ℂ)) *
        (Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) := by
  by_cases hr : r = 0
  · subst r
    simp [Complex.besselJ_zero]
  · rw [hW r hr]
    ring

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
        exact wronskianBesselIntegrand_eq_one_sq_div Y0 Y1 hW r
    _ = (((2 / Real.pi : ℝ) : ℂ)) *
          (∫ r in (0 : ℝ)..R,
            Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = _ := by
        rw [integral_besselJ_one_sq_div]
        simp [Complex.besselJ_zero]

/-- The entire Wronskian-reduced Bessel part of the Bessel radial moment is
evaluated: the radial-cutoff limit is exactly 1/π.

This statement concerns only the mathematical radial integral; it does
not identify a regulated physical integral or any disorder limit. -/
theorem tendsto_integral_wronskianBesselIntegrand
    (Y0 Y1 : ℝ → ℂ) (hW : RealWronskianCondition Y0 Y1) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        Complex.besselJ 1 (r : ℂ) ^ 2 *
          (Complex.besselJ 1 (r : ℂ) * Y0 r -
            Complex.besselJ 0 (r : ℂ) * Y1 r))
      Filter.atTop (nhds ((((2 / Real.pi : ℝ) : ℂ)) * (1 / 2 : ℂ))) := by
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
  exact hlimit.congr' (Filter.Eventually.of_forall hpoint)


/-- The Wronskian-reduced Wronskian-weighted Bessel moment has the exact
universal limit `1/π`, independently of the concrete Y-Bessel
implementation, as soon as the Wronskian condition is established. -/
theorem tendsto_integral_wronskianBesselIntegrand_one_div_pi
    (Y0 Y1 : ℝ → ℂ) (hW : RealWronskianCondition Y0 Y1) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        Complex.besselJ 1 (r : ℂ) ^ 2 *
          (Complex.besselJ 1 (r : ℂ) * Y0 r -
            Complex.besselJ 0 (r : ℂ) * Y1 r))
      Filter.atTop (nhds (((1 / Real.pi : ℝ) : ℂ))) := by
  have hscale : (((2 / Real.pi : ℝ) : ℂ)) * (1 / 2 : ℂ) =
      ((1 / Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [hscale] using
    (tendsto_integral_wronskianBesselIntegrand Y0 Y1 hW)


end

end BesselRadialMoments
