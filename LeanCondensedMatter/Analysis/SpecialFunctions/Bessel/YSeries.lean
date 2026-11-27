import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Second-kind Bessel Y₀ and Y₁: harmonic-number power series

An explicit **convergent** realization of the DLMF 10.8.2 logarithmic
series for the order-zero Bessel function of the second kind:

  Y₀(z) = (2/π) ((log(z/2)+γ) J₀(z) - Σ Hₙ(-z²/4)ⁿ/(n!)²).

The harmonic correction has infinite radius of absolute convergence,
proved here against the ordinary exponential series. The explicit
logarithm uses the principal complex branch and the existing Mathlib
Euler–Mascheroni constant.

The function must be used on the slit plane, away from zero. Lean's
total `Complex.log 0` is not the physical limiting value.

This module only establishes a genuine convergent definition and
elementary normalization; the Bessel ODE, derivative Y₁=-Y₀′,
normalization of the J/Y Wronskian, and outgoing Hankel transform
are separate proof obligations. In particular, merely defining Y₀ does not prove its
Wronskian with J₀ or J₁.
-/

namespace BesselSecondKind

noncomputable section

/-- The rational harmonic number is nonnegative and at most its index,
viewed as a real number. Used to give the logarithmic Y₀ correction
a direct exponential majorant independent of any Bessel-Y axioms. -/
theorem harmonic_real_nonneg_le (n : ℕ) :
    0 ≤ (harmonic n : ℝ) ∧ (harmonic n : ℝ) ≤ (n : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hfrac : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
      have hfrac_le : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        rw [← one_div]
        exact (div_le_iff₀ hp).2 (by simpa only [one_mul] using hn)
      have hcast : (harmonic (n + 1) : ℝ) =
          (harmonic n : ℝ) + (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [harmonic_succ]
        push_cast
        rfl
      rw [hcast]
      constructor
      · exact add_nonneg ih.1 hfrac
      · simpa only [Nat.cast_add, Nat.cast_one] using
          (add_le_add ih.2 hfrac_le)

/-- The analytic correction coefficient appearing in the DLMF
order-zero second-kind Bessel series, with sign chosen so the Y₀
formula contains its subtraction. -/
noncomputable def besselY0HarmonicTerm (z : ℂ) (n : ℕ) : ℂ :=
  ((harmonic n : ℝ) : ℂ) * (-(z / 2) ^ 2) ^ n /
    ((n.factorial : ℂ) ^ 2)

/-- A factorial bound on a nonnegative real coefficient gives an exponential-series
majorant for its normalized complex power term. -/
private theorem norm_factorial_normalized_term_le (h C : ℝ) (x : ℂ) (n m : ℕ)
    (hh : 0 ≤ h) (hC : h ≤ C * (m.factorial : ℝ)) :
    ‖(h : ℂ) * x ^ n / ((n.factorial : ℂ) * (m.factorial : ℂ))‖ ≤
      C * (‖x‖ ^ n / (n.factorial : ℝ)) := by
  have hn : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hm : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc
    _ = h * ‖x‖ ^ n / ((n.factorial : ℝ) * (m.factorial : ℝ)) := by
      simp only [norm_div, norm_mul, norm_pow, Complex.norm_real,
        Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ (C * (m.factorial : ℝ)) * ‖x‖ ^ n /
          ((n.factorial : ℝ) * (m.factorial : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (pow_nonneg (norm_nonneg x) n))
        (mul_nonneg hn.le hm.le)
    _ = _ := by field_simp

/-- The absolute value of each harmonic correction term is dominated
by the factorial exponential term of argument `‖z/2‖²`. -/
theorem norm_besselY0HarmonicTerm_le_expTerm (z : ℂ) (n : ℕ) :
    ‖besselY0HarmonicTerm z n‖ ≤
      (‖z / 2‖ ^ 2) ^ n / (n.factorial : ℝ) := by
  have hH := harmonic_real_nonneg_le n
  have hHfac : (harmonic n : ℝ) ≤ (n.factorial : ℝ) :=
    hH.2.trans (by exact_mod_cast Nat.self_le_factorial n)
  have hb : (harmonic n : ℝ) ≤ 1 * (n.factorial : ℝ) := by
    rw [one_mul]
    exact hHfac
  have h := norm_factorial_normalized_term_le (harmonic n : ℝ) 1 (-(z / 2) ^ 2) n n hH.1 hb
  rw [norm_neg, norm_pow, one_mul] at h
  unfold besselY0HarmonicTerm
  rw [pow_two (n.factorial : ℂ)]
  exact h

/-- The DLMF harmonic-number correction is absolutely summable for
**every** complex argument, including the origin. No informal
rearrangement of conditionally convergent special-function series. -/
theorem summable_besselY0HarmonicTerm (z : ℂ) :
    Summable (besselY0HarmonicTerm z) :=
  Summable.of_norm_bounded
    (Real.summable_pow_div_factorial (‖z / 2‖ ^ 2))
    (norm_besselY0HarmonicTerm_le_expTerm z)

/-- An entire-series correction to the logarithmic order-zero
second-kind Bessel function. The logarithmic singularity is not part
of this correction. -/
noncomputable def besselY0HarmonicCorrection (z : ℂ) : ℂ :=
  ∑' n : ℕ, besselY0HarmonicTerm z n

/-- The power-series correction vanishes at zero; the nonanalytic
part of the physical Y₀ comes solely from its logarithm. -/
@[simp] theorem besselY0HarmonicCorrection_zero :
    besselY0HarmonicCorrection 0 = 0 := by
  unfold besselY0HarmonicCorrection
  have hterm (n : ℕ) : besselY0HarmonicTerm 0 n = 0 := by
    cases n with
    | zero => simp [besselY0HarmonicTerm]
    | succ n => simp [besselY0HarmonicTerm]
  simp only [hterm, tsum_zero]

/-- DLMF 10.8.2, with Mathlib's canonical Euler–Mascheroni constant.
The function is interpreted on nonzero complex arguments in the
principal logarithm branch; the zero argument is only a totalized
Lean value, not a claim that Y₀ extends continuously to the origin. -/
noncomputable def besselY0Series (z : ℂ) : ℂ :=
  (((2 / Real.pi : ℝ) : ℂ)) *
    ((Complex.log (z / 2) + (Real.eulerMascheroniConstant : ℂ)) *
        Complex.besselJ 0 z - besselY0HarmonicCorrection z)

end

end BesselSecondKind

/-!
## Order-one second-kind Bessel Y₁: explicit harmonic-number series

The explicit DLMF 10.8.1 series for integer order one is
reorganized using the harmonic numbers and Euler's constant:

  Y₁(z) = (2/π) [-1/z + (log(z/2)+γ) J₁(z)
                         - (z/4) Σ (Hₙ+Hₙ₊₁) (-z²/4)ⁿ/(n!(n+1)!)].

We establish the *actual absolute convergence* of the correction
series for every complex z using an exponential majorant. The
singular `-2/(πz)` term is retained explicitly, not silently
discarded by a totalized inverse at zero.

The derivative identity Y₁=-Y₀', the second-kind Bessel equation
and its Wronskian with J₀/J₁ are mathematical goals, NOT assumptions
or conclusions in this file. An explicit convergent formula alone
does not by itself establish the Wronskian.
-/

namespace BesselSecondKind

noncomputable section

/-- The combined rational harmonic coefficient in DLMF's order-one
second-kind Bessel power series. -/
noncomputable def besselY1HarmonicTerm (z : ℂ) (n : ℕ) : ℂ :=
  (((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) : ℂ) *
    (-(z / 2) ^ 2) ^ n /
    ((n.factorial : ℂ) * ((n + 1).factorial : ℂ))

/-- The combined real harmonic coefficient is bounded by twice the
factorial of the higher index; the corrected series is dominated
by two copies of the ordinary exponential series. -/
theorem besselY1Harmonic_nonneg_le_factorial (n : ℕ) :
    0 ≤ ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) ∧
      ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) ≤
        2 * ((n + 1).factorial : ℝ) := by
  have hn := harmonic_real_nonneg_le n
  have hs := harmonic_real_nonneg_le (n + 1)
  have hfac : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.self_le_factorial (n + 1)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  constructor <;> linarith

/-- Direct absolute convergence estimate for the order-one harmonic
series coefficient. -/
theorem norm_besselY1HarmonicTerm_le_two_expTerm (z : ℂ) (n : ℕ) :
    ‖besselY1HarmonicTerm z n‖ ≤
      2 * ((‖z / 2‖ ^ 2) ^ n / (n.factorial : ℝ)) := by
  have hH := besselY1Harmonic_nonneg_le_factorial n
  have h := norm_factorial_normalized_term_le
    ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) 2 (-(z / 2) ^ 2) n (n + 1)
    hH.1 hH.2
  rw [norm_neg, norm_pow] at h
  simpa only [besselY1HarmonicTerm, Complex.ofReal_add] using h

/-- The order-one second-kind Bessel harmonic correction converges
absolutely everywhere in the complex plane. -/
theorem summable_besselY1HarmonicTerm (z : ℂ) :
    Summable (besselY1HarmonicTerm z) := by
  apply Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (‖z / 2‖ ^ 2)).mul_left 2)
  exact norm_besselY1HarmonicTerm_le_two_expTerm z

/-- The analytic correction for the order-one Bessel Y function. -/
noncomputable def besselY1HarmonicCorrection (z : ℂ) : ℂ :=
  ∑' n : ℕ, besselY1HarmonicTerm z n

/-- DLMF 10.8.1 specialized to order one, including the full
negative `2/(π z)` pole and the correct `z/(2π)` series prefactor. -/
noncomputable def besselY1Series (z : ℂ) : ℂ :=
  (((2 / Real.pi : ℝ) : ℂ)) *
    (-(z⁻¹) +
      (Complex.log (z / 2) + (Real.eulerMascheroniConstant : ℂ)) *
        Complex.besselJ 1 z -
      (z / 4) * besselY1HarmonicCorrection z)


/-- Exact Wronskian algebra for the *concrete* convergent DLMF Y₀/Y₁
series. The logarithm and Euler–Mascheroni terms cancel completely.
Thus the sole remaining nonalgebraic Wronskian obligation is an identity
between Mathlib J₀/J₁ and the two convergent harmonic corrections.
This theorem does **not** assume or prove that remaining identity. -/
theorem besselY0Y1Wronskian_eq_harmonicCorrections (z : ℂ) :
    Complex.besselJ 1 z * besselY0Series z -
      Complex.besselJ 0 z * besselY1Series z =
    (((2 / Real.pi : ℝ) : ℂ)) *
      (Complex.besselJ 0 z * z⁻¹ -
        Complex.besselJ 1 z * besselY0HarmonicCorrection z +
        (z / 4) * Complex.besselJ 0 z * besselY1HarmonicCorrection z) := by
  unfold besselY0Series besselY1Series
  ring

/-- Reduction of the J/Y Wronskian theorem to one explicit
harmonic-number series identity. The hypothesis is kept visible
rather than incorrectly presenting the Wronskian as proved. -/
theorem besselY0Y1Wronskian_of_harmonicIdentity
    (z : ℂ) (hz : z ≠ 0)
    (hidentity :
      Complex.besselJ 0 z -
          z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
          (z ^ 2 / 4) * Complex.besselJ 0 z *
            besselY1HarmonicCorrection z = 1) :
    Complex.besselJ 1 z * besselY0Series z -
      Complex.besselJ 0 z * besselY1Series z =
        (((2 / Real.pi : ℝ) : ℂ)) * z⁻¹ := by
  rw [besselY0Y1Wronskian_eq_harmonicCorrections]
  congr 1
  apply (mul_left_cancel₀ hz)
  calc
    _ = Complex.besselJ 0 z -
          z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
          (z ^ 2 / 4) * Complex.besselJ 0 z *
            besselY1HarmonicCorrection z := by field_simp [hz]
    _ = 1 := hidentity
    _ = z * z⁻¹ := by field_simp [hz]

end

end BesselSecondKind
