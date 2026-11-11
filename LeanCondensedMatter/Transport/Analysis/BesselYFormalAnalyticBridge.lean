import LeanCondensedMatter.Transport.Analysis.BesselYFormalOrderOne
import LeanCondensedMatter.Transport.Analysis.BesselY1Series

set_option linter.style.header false

/-!
# Exact term-level bridge between formal and convergent Y harmonic series

The formal coefficient calculations in BesselYFormalOrderOne are for
power-series coefficients `A,B,C`. This module verifies that the
realized DLMF harmonic corrections from merged PR #4529 are **exactly**
the coefficientwise `tsum` evaluations of `B` and `C` at
`x=-(z/2)²`. No change of analytic functions, no new hypothesis,
and no shortcut using a topologically nilpotent formal-power-series
evaluation at arbitrary complex arguments.

This identifies the precise analytic bridge still required:
a theorem transporting the formal products and derivatives through
their absolutely convergent complex series.
-/

namespace QuantumTheory.Transport

noncomputable section

/-- The n-th actual Y₀ harmonic correction summand is the
corresponding formal coefficient evaluated at x=-(z/2)². -/
theorem besselY0HarmonicTerm_eq_formal (z : ℂ) (n : ℕ) :
    besselY0HarmonicTerm z n =
      PowerSeries.coeff n besselFormalH0 * (-(z / 2) ^ 2) ^ n := by
  simp only [besselY0HarmonicTerm, besselFormalH0, PowerSeries.coeff_mk]
  simp only [div_eq_mul_inv]
  ring_nf

/-- A real, absolutely convergent second-kind Y₀ correction is
the termwise sum of the **proved formal** harmonic coefficients. -/
theorem besselY0HarmonicCorrection_eq_formalTsum (z : ℂ) :
    besselY0HarmonicCorrection z =
      ∑' n : ℕ, PowerSeries.coeff n besselFormalH0 *
        (-(z / 2) ^ 2) ^ n := by
  unfold besselY0HarmonicCorrection
  apply tsum_congr
  intro n
  exact besselY0HarmonicTerm_eq_formal z n

/-- The coefficientwise evaluation of the formal H₀ series converges
absolutely at every complex argument, by the already proved concrete
Y₀ harmonic-term bound. -/
theorem summable_besselFormalH0_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH0 * (-(z / 2) ^ 2) ^ n) := by
  simpa only [← besselY0HarmonicTerm_eq_formal] using
    (summable_besselY0HarmonicTerm z)

/-- The n-th actual Y₁ harmonic correction summand is the
corresponding order-one formal coefficient. -/
theorem besselY1HarmonicTerm_eq_formal (z : ℂ) (n : ℕ) :
    besselY1HarmonicTerm z n =
      PowerSeries.coeff n besselFormalH1 * (-(z / 2) ^ 2) ^ n := by
  simp only [besselY1HarmonicTerm, besselFormalH1, PowerSeries.coeff_mk]
  simp only [div_eq_mul_inv]
  ring_nf

/-- The actual absolutely convergent Y₁ correction
is the precise coefficientwise evaluation of its formal series. -/
theorem besselY1HarmonicCorrection_eq_formalTsum (z : ℂ) :
    besselY1HarmonicCorrection z =
      ∑' n : ℕ, PowerSeries.coeff n besselFormalH1 *
        (-(z / 2) ^ 2) ^ n := by
  unfold besselY1HarmonicCorrection
  apply tsum_congr
  intro n
  exact besselY1HarmonicTerm_eq_formal z n

/-- The coefficientwise evaluation of the formal H₁ series also
converges absolutely at every complex argument. -/
theorem summable_besselFormalH1_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH1 * (-(z / 2) ^ 2) ^ n) := by
  simpa only [← besselY1HarmonicTerm_eq_formal] using
    (summable_besselY1HarmonicTerm z)

end

end QuantumTheory.Transport
