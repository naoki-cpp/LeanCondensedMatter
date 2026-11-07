import LeanCondensedMatter.Transport.Analysis.BesselRadialMoments

set_option linter.style.header false

/-!
# Wronskian-reduced crossed-X Bessel radial moment

The standard massive-Dirac Gaussian-crossed X benchmark contains the
scalar Bessel integral

  ∫₀^R J₁(s)² (J₁(s) Y₀(s) - J₀(s) Y₁(s)) ds.

The first/second-kind Bessel Wronskian reduces its parenthesis to
2 / (π s) for every positive `s`. The existing project theorem
`integral_besselJ_one_sq_div` then evaluates the full finite interval
*exactly*, and `tendsto_integral_besselJ_one_sq_div` proves the large-
radius limit, without an assumption of absolute integrability at infinity.

Mathlib v4.35.0 currently supplies `Complex.besselJ` but not a canonical
second-kind Bessel-Y API. Accordingly `Y0` and `Y1` are parameters,
and their Wronskian is an *explicit theorem hypothesis* (not an axiom).
Identifying the finite-regulator physical X Hall integral with this
Bessel moment, including weak disorder and the renormalized spectral
boundary, is a separate and presently unproved obligation.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- The first/second-kind Wronskian condition at nonzero real arguments.
This is the exact input needed to eliminate the Y-Bessel functions from
the Ado crossed-X radial moment; no singular value at zero is demanded. -/
def CrossedXBesselWronskian (Y0 Y1 : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, r ≠ 0 →
    Complex.besselJ 1 (r : ℂ) * Y0 r -
      Complex.besselJ 0 (r : ℂ) * Y1 r =
      (((2 / Real.pi : ℝ) : ℂ)) * (r : ℂ)⁻¹

/-- Exact Wronskian reduction of the X radial integrand, including the
origin via the continuous J₁²/r extension. -/
theorem crossedXBesselIntegrand_eq_one_sq_div
    (Y0 Y1 : ℝ → ℂ) (hW : CrossedXBesselWronskian Y0 Y1)
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

/-- The finite-radius Gaussian crossed X Bessel integral is an explicit
endpoint expression, under only the standard Wronskian condition.
The Y functions never need values or continuity at r=0. -/
theorem integral_crossedXBesselIntegrand_eq_endpoints
    (Y0 Y1 : ℝ → ℂ) (hW : CrossedXBesselWronskian Y0 Y1)
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
        exact crossedXBesselIntegrand_eq_one_sq_div Y0 Y1 hW r
    _ = (((2 / Real.pi : ℝ) : ℂ)) *
          (∫ r in (0 : ℝ)..R,
            Complex.besselJ 1 (r : ℂ) ^ 2 / (r : ℂ)) := by
        rw [intervalIntegral.integral_const_mul]
    _ = _ := by
        rw [integral_besselJ_one_sq_div]
        simp [Complex.besselJ_zero]

/-- The entire Wronskian-reduced Bessel part of the Ado X diagram is
evaluated: the radial-cutoff limit is exactly 1/π.

This theorem does not identify the physical finite-Born X diagram with
the Bessel integrand; in particular no ultraviolet, zero-broadening,
weak-disorder or real-space Fourier limit is smuggled into the statement. -/
theorem tendsto_integral_crossedXBesselIntegrand
    (Y0 Y1 : ℝ → ℂ) (hW : CrossedXBesselWronskian Y0 Y1) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        Complex.besselJ 1 (r : ℂ) ^ 2 *
          (Complex.besselJ 1 (r : ℂ) * Y0 r -
            Complex.besselJ 0 (r : ℂ) * Y1 r))
      Filter.atTop (nhds ((((2 / Real.pi : ℝ) : ℂ)) * (1 / 2 : ℂ))) := by
  have hlimit := (tendsto_integral_besselJ_one_sq_div).const_mul
    (((2 / Real.pi : ℝ) : ℂ))
  exact hlimit.congr' (Filter.Eventually.of_forall fun R =>
    (integral_crossedXBesselIntegrand_eq_endpoints Y0 Y1 hW R).symm.trans
      (by
        rw [integral_besselJ_one_sq_div]
        simp [Complex.besselJ_zero]))

end

end Transport
end QuantumTheory
