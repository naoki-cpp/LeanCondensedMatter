import LeanCondensedMatter.Analysis.PowerSeries.CoefficientSum
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.FormalCoefficients
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.Y1Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Formal J/Y-series bridges and unconditional analytic Bessel J/Y Wronskian

Transport the normalized formal J₀/H₀/H₁ harmonic identity from ℂ⟦X⟧
to absolutely convergent complex series using coefficientwise evaluations
and the proven power-series Cauchy-product theorems. The result is the
unconditional J/Y Wronskian for the concrete DLMF second-kind series
at nonzero complex arguments. The exact termwise J- and Y-series bridges are proved first.

This module does not depend on transport, Fourier geometry or physical models.
-/

/-!
# Analytic J₀/J₁ bridge for the formal factorial series

The formal series `besselFormalJ0` is the unique normalized factorial
coefficient series already used in the unconditional formal Wronskian proof.
We identify its coefficients, and the coefficients of its formal derivative,
with Mathlib's regularized hypergeometric coefficients of parameters 1 and 2.

This gives actual, everywhere-summable complex `tsum` formulas
for `Complex.besselJ 0 z` and `Complex.besselJ 1 z` at
`x = -(z/2)^2`, with no invented evaluation of `ℂ⟦X⟧` at non-nilpotent
arguments. Transporting products through these evaluations requires a
separate Cauchy-product theorem.
-/

namespace BesselFormal

open BesselHypergeometric

open BesselFormal

noncomputable section

/-- The formal J₀ factorial coefficient agrees with the *actual*
regularized hypergeometric coefficient for bottom parameter 1. -/
theorem besselFormalJ0_coeff_eq_regularizedHGFun (n : ℕ) :
    PowerSeries.coeff n besselFormalJ0 =
      Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n := by
  have h := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 n
  simpa [besselFormalJ0, pow_two] using h.symm

/-- The formal derivative of J₀ has exactly the bottom-parameter-2
hypergeometric coefficients. This is a coefficient-level statement,
not analytic differentiation of an infinite sum. -/
theorem besselFormalJ0_derivative_coeff_eq_regularizedHGFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) =
      Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n := by
  have hcoeff :
      Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n =
        1 / ((Nat.factorial n : ℂ) * (Nat.factorial (n + 1) : ℂ)) := by
    simpa using (regularizedHGFunCoeff_zero_singleton_nat_add_one 1 n)
  rw [PowerSeries.coeff_derivative, hcoeff]
  simp only [besselFormalJ0, PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]

/-- Formal J₀ coefficients have an everywhere convergent complex
power-series evaluation, by the known entire hypergeometric series. -/
theorem summable_besselFormalJ0_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalJ0 * (-(z / 2) ^ 2) ^ n) := by
  have hs :
      Summable (fun n : ℕ =>
        Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n * (-(z / 2) ^ 2) ^ n) := by
    simpa only [Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
        (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).summable (by simp)
  simpa only [besselFormalJ0_coeff_eq_regularizedHGFun] using hs

/-- Formal J₀ derivative coefficients also have an everywhere
convergent complex evaluation. -/
theorem summable_besselFormalJ0_derivative_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
        (-(z / 2) ^ 2) ^ n) := by
  have hs :
      Summable (fun n : ℕ =>
        Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n * (-(z / 2) ^ 2) ^ n) := by
    simpa only [Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
        (Complex.regularizedHGFunSeries 0 {(2 : ℂ)}).summable (by simp)
  simpa only [besselFormalJ0_derivative_coeff_eq_regularizedHGFun] using hs

/-- Mathlib's J₀ is the coefficientwise entire evaluation of the
concrete formal factorial power series. -/
theorem besselJZero_eq_formalTsum (z : ℂ) :
    Complex.besselJ 0 z =
      ∑' n : ℕ, PowerSeries.coeff n besselFormalJ0 *
        (-(z / 2) ^ 2) ^ n := by
  rw [besselJZero_eq_regularizedHGTsum]
  apply tsum_congr
  intro n
  rw [besselFormalJ0_coeff_eq_regularizedHGFun]

/-- Analytic J₁ is the complex evaluation of the *formal derivative*
of the normalized J₀ factorial series, multiplied by z/2. No analytic
derivative-of-sum exchange is postulated. -/
theorem besselJOne_eq_formalDerivativeTsum (z : ℂ) :
    Complex.besselJ 1 z =
      (z / 2) * (∑' n : ℕ,
        PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
          (-(z / 2) ^ 2) ^ n) := by
  calc
    Complex.besselJ 1 z =
        (z / 2) * Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2) := by
      simp only [Complex.besselJ_def, Complex.cpow_one]
      congr 1
      norm_num
    _ = (z / 2) * (∑' n : ℕ,
          PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
            (-(z / 2) ^ 2) ^ n) := by
      congr 1
      rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
        ← FormalMultilinearSeries.ofScalarsSum,
        FormalMultilinearSeries.ofScalars_sum_eq]
      simp only [smul_eq_mul]
      apply tsum_congr
      intro n
      rw [besselFormalJ0_derivative_coeff_eq_regularizedHGFun]

end

end BesselFormal

/-!
# Formal-to-analytic bridge between formal and convergent Y harmonic series

The formal coefficient calculations in FormalCoefficients are for
power-series coefficients `A,B,C`. This module verifies that the
realized DLMF harmonic corrections from merged PR #4529 are **exactly**
the coefficientwise `tsum` evaluations of `B` and `C` at
`x=-(z/2)²`. No change of analytic functions, no new hypothesis,
and no shortcut using a topologically nilpotent formal-power-series
evaluation at arbitrary complex arguments.

The equivalence is a termwise identity with absolutely convergent sums.
Polynomial products and formal Wronskian identities are transported
through these evaluations in the analytic Wronskian results below.
-/

namespace BesselSecondKind

open BesselFormal

noncomputable section

/-- The n-th actual Y₀ harmonic correction summand is the
corresponding formal coefficient evaluated at x=-(z/2)². -/
theorem besselY0HarmonicTerm_eq_formal (z : ℂ) (n : ℕ) :
    besselY0HarmonicTerm z n =
      PowerSeries.coeff n besselFormalH0 * (-(z / 2) ^ 2) ^ n := by
  simp only [besselY0HarmonicTerm, besselFormalH0, PowerSeries.coeff_mk]
  simp only [div_eq_mul_inv, Complex.ofReal_ratCast]
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
  simp only [div_eq_mul_inv, Complex.ofReal_ratCast]
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

end BesselSecondKind

namespace BesselSecondKind

open BesselFormal

noncomputable section

open scoped PowerSeries

/-- The missing harmonic identity for the *actual* Mathlib J₀/J₁ and
the absolutely convergent DLMF Y₀/Y₁ harmonic corrections. -/
theorem besselY0Y1_harmonicIdentity (z : ℂ) :
    Complex.besselJ 0 z -
        z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
        (z ^ 2 / 4) * Complex.besselJ 0 z *
          besselY1HarmonicCorrection z = 1 := by
  let x : ℂ := -(z / 2) ^ 2
  have hA : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalJ0 * x ^ n) :=
    summable_besselFormalJ0_eval z
  have hD : Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) * x ^ n) :=
    summable_besselFormalJ0_derivative_eval z
  have hB : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH0 * x ^ n) :=
    summable_besselFormalH0_eval z
  have hC : Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalH1 * x ^ n) :=
    summable_besselFormalH1_eval z
  have htwo : PowerSeries.C (2 : ℂ) = (2 : ℂ⟦X⟧) :=
    map_natCast (PowerSeries.C : ℂ →+* ℂ⟦X⟧) 2
  have h2D : Summable (fun n : ℕ =>
      PowerSeries.coeff n (2 * PowerSeries.derivative besselFormalJ0) * x ^ n) := by
    simpa only [htwo] using PowerSeries.summable_coefficientSum_C_mul
      (PowerSeries.derivative besselFormalJ0) x 2 hD
  have h2DEval :
      PowerSeries.coefficientSum (2 * PowerSeries.derivative besselFormalJ0) x =
        2 * PowerSeries.coefficientSum (PowerSeries.derivative besselFormalJ0) x := by
    simpa only [htwo] using PowerSeries.coefficientSum_C_mul (PowerSeries.derivative besselFormalJ0) x 2
  have h2DB :=
    PowerSeries.summable_coefficientSum_mul
      (2 * PowerSeries.derivative besselFormalJ0) besselFormalH0 x h2D hB
  have hAC :=
    PowerSeries.summable_coefficientSum_mul
      besselFormalJ0 besselFormalH1 x hA hC
  have hX2DB :=
    PowerSeries.summable_coefficientSum_X_mul
      (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) x h2DB
  have hXAC :=
    PowerSeries.summable_coefficientSum_X_mul
      (besselFormalJ0 * besselFormalH1) x hAC
  have hAplus :=
    PowerSeries.summable_coefficientSum_add besselFormalJ0
      (PowerSeries.X * (2 * PowerSeries.derivative besselFormalJ0 *
        besselFormalH0)) x hA hX2DB
  have hFormal := congrArg
    (fun f : ℂ⟦X⟧ => PowerSeries.coefficientSum f x)
    besselFormalJ0H0H1_harmonicIdentity
  rw [PowerSeries.coefficientSum_sub _ _ x hAplus hXAC,
      PowerSeries.coefficientSum_add _ _ x hA hX2DB,
      PowerSeries.coefficientSum_X_mul
        (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) x,
      PowerSeries.coefficientSum_X_mul (besselFormalJ0 * besselFormalH1) x,
      PowerSeries.coefficientSum_mul _ _ x h2D hB,
      PowerSeries.coefficientSum_mul _ _ x hA hC,
      h2DEval,
      PowerSeries.coefficientSum_one] at hFormal
  have hJ0 :
      PowerSeries.coefficientSum besselFormalJ0 x =
        Complex.besselJ 0 z :=
    (besselJZero_eq_formalTsum z).symm
  have hJ1 :
      (z / 2) *
          PowerSeries.coefficientSum
            (PowerSeries.derivative besselFormalJ0) x =
        Complex.besselJ 1 z :=
    (besselJOne_eq_formalDerivativeTsum z).symm
  have hY0 :
      PowerSeries.coefficientSum besselFormalH0 x =
        besselY0HarmonicCorrection z :=
    (besselY0HarmonicCorrection_eq_formalTsum z).symm
  have hY1 :
      PowerSeries.coefficientSum besselFormalH1 x =
        besselY1HarmonicCorrection z :=
    (besselY1HarmonicCorrection_eq_formalTsum z).symm
  calc
    Complex.besselJ 0 z -
        z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
        (z ^ 2 / 4) * Complex.besselJ 0 z * besselY1HarmonicCorrection z =
      PowerSeries.coefficientSum besselFormalJ0 x +
        x * (2 * PowerSeries.coefficientSum
          (PowerSeries.derivative besselFormalJ0) x *
          PowerSeries.coefficientSum besselFormalH0 x) -
        x * (PowerSeries.coefficientSum besselFormalJ0 x *
          PowerSeries.coefficientSum besselFormalH1 x) := by
        rw [← hJ0, ← hJ1, ← hY0, ← hY1]
        dsimp [x]
        ring
    _ = 1 := hFormal

/-- The actual convergent DLMF Y₀/Y₁ series satisfy the standard
normalized J/Y Wronskian for every nonzero complex argument. -/
theorem besselY0Y1Series_wronskian (z : ℂ) (hz : z ≠ 0) :
    Complex.besselJ 1 z * besselY0Series z -
      Complex.besselJ 0 z * besselY1Series z =
        (((2 / Real.pi : ℝ) : ℂ)) * z⁻¹ :=
  besselY0Y1Wronskian_of_harmonicIdentity z hz
    (besselY0Y1_harmonicIdentity z)

/-- The first/second-kind Wronskian condition at nonzero real arguments.
The normalization is independent of any particular transport integral.
No singular value at zero is demanded. -/
def RealWronskianCondition (Y0 Y1 : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, r ≠ 0 →
    Complex.besselJ 1 (r : ℂ) * Y0 r -
      Complex.besselJ 0 (r : ℂ) * Y1 r =
      (((2 / Real.pi : ℝ) : ℂ)) * (r : ℂ)⁻¹

/-- The concrete absolutely convergent second-kind Bessel series
satisfy the real-argument normalization condition by restricting
the proved complex Wronskian to the real axis. -/
theorem realWronskianCondition_concreteSeries :
    RealWronskianCondition
      (fun r : ℝ => besselY0Series (r : ℂ))
      (fun r : ℝ => besselY1Series (r : ℂ)) := by
  intro r hr
  exact besselY0Y1Series_wronskian (r : ℂ) (by exact_mod_cast hr)
end

end BesselSecondKind
