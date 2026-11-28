import LeanCondensedMatter.Analysis.PowerSeries.FrobeniusWronskian
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import LeanCondensedMatter.Analysis.PowerSeries.CoefficientSum
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.YSeries
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Bessel J/Y Wronskian: formal coefficients and analytic evaluation

The factorial coefficient sequence `aₙ=1/(n!)²` and the
harmonic correction sequence `bₙ=Hₙ/(n!)²` realize two
formal power series `A` and `B`.

Their coefficient recurrences are

  (n+1)² aₙ₊₁ = aₙ
  (n+1)² bₙ₊₁ = bₙ + (n+1) aₙ₊₁.

As a result, `A` and `B` satisfy the Frobenius formal
differential equations

  d/dx (x A') = A
  d/dx (x B') = B + A'.

The formal identities in `ℂ⟦X⟧` include the order-one harmonic correction.
Absolutely convergent coefficient evaluations identify these series with the
analytic J₀, J₁, Y₀ and Y₁ functions and give their Wronskian at nonzero complex
arguments. No transport or physical-model assumptions are required.
-/

namespace BesselFormal

noncomputable section

open scoped PowerSeries

/-- Zeroth-order Frobenius Bessel-J coefficients. -/
noncomputable def besselFormalJ0 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ => (((n.factorial : ℂ) ^ 2))⁻¹

/-- Frobenius harmonic correction coefficients of Bessel Y₀. -/
noncomputable def besselFormalH0 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ =>
    (harmonic n : ℂ) / ((n.factorial : ℂ) ^ 2)

/-- The J₀ Frobenius coefficients satisfy the Bessel recurrence
without any convergence assumptions. -/
theorem besselFormalJ0_coeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ 2 *
      PowerSeries.coeff (n + 1) besselFormalJ0 =
        PowerSeries.coeff n besselFormalJ0 := by
  simp only [besselFormalJ0, PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]

private theorem harmonic_succ_complex (n : ℕ) :
    (harmonic (n + 1) : ℂ) =
      (harmonic n : ℂ) + (((n + 1 : ℕ) : ℂ))⁻¹ := by
  rw [harmonic_succ]
  push_cast
  rfl

/-- The harmonic-number recurrence produces the inhomogeneous
Frobenius equation for the Y₀ entire correction. -/
theorem besselFormalH0_coeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ 2 *
      PowerSeries.coeff (n + 1) besselFormalH0 =
        PowerSeries.coeff n besselFormalH0 +
          ((n + 1 : ℕ) : ℂ) *
            PowerSeries.coeff (n + 1) besselFormalJ0 := by
  simp only [besselFormalH0, besselFormalJ0, PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [harmonic_succ_complex, Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]

/-- The concrete factorial series solves the homogeneous
order-zero Frobenius equation in the formal power-series ring. -/
theorem besselFormalJ0_frobenius :
    PowerSeries.derivative
      (PowerSeries.X * PowerSeries.derivative besselFormalJ0) =
      besselFormalJ0 := by
  apply PowerSeries.ext
  intro n
  rw [FrobeniusWronskian.coeff_derivative_X_mul_derivative]
  exact besselFormalJ0_coeff_succ n

/-- The concrete harmonic series solves the inhomogeneous
order-zero Frobenius equation in the formal power-series ring. -/
theorem besselFormalH0_frobenius :
    PowerSeries.derivative
      (PowerSeries.X * PowerSeries.derivative besselFormalH0) =
      besselFormalH0 + PowerSeries.derivative besselFormalJ0 := by
  apply PowerSeries.ext
  intro n
  rw [FrobeniusWronskian.coeff_derivative_X_mul_derivative,
    besselFormalH0_coeff_succ, map_add, PowerSeries.coeff_derivative]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- Formal Bessel J₀ and the harmonic correction have exactly
the Frobenius initial coefficients; in particular no singular
logarithm is hidden in the formal correction. -/
@[simp] theorem besselFormalJ0_constantCoeff :
    PowerSeries.constantCoeff besselFormalJ0 = 1 := by
  simp [besselFormalJ0, PowerSeries.constantCoeff_mk]

@[simp] theorem besselFormalH0_constantCoeff :
    PowerSeries.constantCoeff besselFormalH0 = 0 := by
  simp [besselFormalH0, PowerSeries.constantCoeff_mk, harmonic_zero]

/-- Exact **unconditional formal** Wronskian identity for
the factorial and harmonic coefficients. No Wronskian
hypothesis and no imported special-function identity. -/
theorem besselFormalJ0H0_wronskian :
    FrobeniusWronskian.invariant besselFormalJ0 besselFormalH0 = 1 := by
  apply FrobeniusWronskian.invariant_eq_one
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, mul_one, one_mul, add_comm] using
        besselFormalJ0_frobenius
  · simpa only [Derivation.leibniz,
      PowerSeries.derivative_X, smul_eq_mul, mul_one, one_mul, add_comm] using
        besselFormalH0_frobenius
  · exact besselFormalJ0_constantCoeff

end

end BesselFormal

/-!
# Formal Y₁ coefficients and the exact normalized harmonic Wronskian

The order-one correction of the concrete DLMF Y₁ series
is represented by the formal power series

  C(x) = Σ (Hₙ + Hₙ₊₁) xⁿ / (n!(n+1)!).

The harmonic recurrence gives a formal derivative relation

  x C = 2x B' - (A-1),

where A(x)=Σ xⁿ/(n!)² and B(x)=Σ Hₙxⁿ/(n!)²
are the factorial and harmonic formal series.

Inserting this relation into the Frobenius invariant
A²+2x(A'B-AB')=1 yields

  A+2x A'B-x A C=1.

After analytic evaluation at x=-z²/4, this yields the corresponding
complex Bessel J/Y harmonic-series identity through absolutely summable
coefficient evaluation and the Cauchy-product theorem.
-/

namespace BesselFormal

noncomputable section

open scoped PowerSeries

/-- Exact order-one harmonic correction as a **formal**
power series with DLMF coefficients. -/
noncomputable def besselFormalH1 : ℂ⟦X⟧ :=
  PowerSeries.mk fun n : ℕ =>
    ((harmonic n : ℂ) + (harmonic (n + 1) : ℂ)) /
      ((n.factorial : ℂ) * ((n + 1).factorial : ℂ))

/-- The single coefficient identity linking order-one harmonic
corrections to the derivative of the order-zero correction. -/
theorem besselFormalH1_coeff (n : ℕ) :
    PowerSeries.coeff n besselFormalH1 =
      2 * ((n + 1 : ℕ) : ℂ) *
          PowerSeries.coeff (n + 1) besselFormalH0 -
        PowerSeries.coeff (n + 1) besselFormalJ0 := by
  simp only [besselFormalH1, besselFormalH0, besselFormalJ0,
    PowerSeries.coeff_mk]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [harmonic_succ_complex, Nat.factorial_succ]
  push_cast
  field_simp [hn, hf]; ring

/-- Precise formal derivative relation behind the order-one
DLMF harmonic correction; no differentiation of a complex
infinite sum is used. -/
theorem besselFormalH1_derivative_relation :
    PowerSeries.X * besselFormalH1 =
      PowerSeries.X * (2 * PowerSeries.derivative besselFormalH0) -
        (besselFormalJ0 - 1) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [besselFormalJ0_constantCoeff,
      PowerSeries.coeff_zero_X_mul]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_derivative]
    simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero]
    calc
      _ = 2 * ((n + 1 : ℕ) : ℂ) *
            PowerSeries.coeff (n + 1) besselFormalH0 -
          PowerSeries.coeff (n + 1) besselFormalJ0 := besselFormalH1_coeff n
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- Formal Wronskian identity for the factorial and harmonic coefficient sequences
of J₀, Y₀ and Y₁, independent of analytic evaluation. -/
theorem besselFormalJ0H0H1_harmonicIdentity :
    besselFormalJ0 +
        PowerSeries.X *
          (2 * PowerSeries.derivative besselFormalJ0 * besselFormalH0) -
        PowerSeries.X * (besselFormalJ0 * besselFormalH1) = 1 := by
  have hW := besselFormalJ0H0_wronskian
  have hC := besselFormalH1_derivative_relation
  unfold FrobeniusWronskian.invariant at hW
  linear_combination hW - besselFormalJ0 * hC

end

end BesselFormal

/-!
## Formal J/Y-series bridges and unconditional analytic Bessel J/Y Wronskian

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
  rw [PowerSeries.coeff_derivative, besselFormalJ0_coeff_eq_regularizedHGFun, mul_comm]
  simpa using regularizedHGFunCoeff_index_shift 0 n

/-- Formal J₀ coefficients have an everywhere convergent complex
power-series evaluation, by the known entire hypergeometric series. -/
theorem summable_besselFormalJ0_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n besselFormalJ0 * (-(z / 2) ^ 2) ^ n) := by
  simpa only [besselFormalJ0_coeff_eq_regularizedHGFun] using
    summable_regularizedHGFun_zero {(1 : ℂ)} (-(z / 2) ^ 2)

/-- Formal J₀ derivative coefficients also have an everywhere
convergent complex evaluation. -/
theorem summable_besselFormalJ0_derivative_eval (z : ℂ) :
    Summable (fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.derivative besselFormalJ0) *
        (-(z / 2) ^ 2) ^ n) := by
  simpa only [besselFormalJ0_derivative_coeff_eq_regularizedHGFun] using
    summable_regularizedHGFun_zero {(2 : ℂ)} (-(z / 2) ^ 2)

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
  have h : Complex.besselJ 1 z =
      (z / 2) * Complex.regularizedHGFun 0 {(2 : ℂ)} (-(z / 2) ^ 2) := by
    simpa using besselJ_nat_eq 1 z
  rw [h, regularizedHGFun_zero_eq_tsum]
  simp only [besselFormalJ0_derivative_coeff_eq_regularizedHGFun]

end

end BesselFormal

/-!
# Formal-to-analytic bridge between formal and convergent Y harmonic series

The DLMF harmonic corrections are coefficientwise `tsum` evaluations
of the formal series `B` and `C` at `x=-(z/2)²`.
Termwise identities and absolute summability justify evaluation of the
formal Wronskian identity and its products at arbitrary complex arguments,
without requiring topological nilpotence of the argument.
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
  have h2D := PowerSeries.hasSum_coefficientSum_C_mul
    (PowerSeries.derivative besselFormalJ0) x 2 hD.hasSum
  rw [htwo] at h2D
  have h2DB := PowerSeries.hasSum_coefficientSum_mul
    (2 * PowerSeries.derivative besselFormalJ0) besselFormalH0 x
    h2D hB.hasSum h2D.summable.norm hB.norm
  have hAC := PowerSeries.hasSum_coefficientSum_mul
    besselFormalJ0 besselFormalH1 x hA.hasSum hC.hasSum hA.norm hC.norm
  have hX2DB := PowerSeries.hasSum_coefficientSum_X_mul _ x h2DB
  have hXAC := PowerSeries.hasSum_coefficientSum_X_mul _ x hAC
  have hAplus := PowerSeries.hasSum_coefficientSum_add _ _ x hA.hasSum hX2DB
  have hFormal := PowerSeries.hasSum_coefficientSum_sub _ _ x hAplus hXAC
  rw [besselFormalJ0H0H1_harmonicIdentity] at hFormal
  have hEval : PowerSeries.coefficientSum (1 : ℂ⟦X⟧) x = _ := hFormal.tsum_eq
  rw [PowerSeries.coefficientSum_one] at hEval
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
    _ = 1 := hEval.symm

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
