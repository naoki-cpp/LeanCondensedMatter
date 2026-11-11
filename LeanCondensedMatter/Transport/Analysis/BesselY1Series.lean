import LeanCondensedMatter.Transport.Analysis.BesselY0Series

set_option linter.style.header false

/-!
# Order-one second-kind Bessel Y₁: explicit harmonic-number series

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
cannot yet discharge `CrossedXBesselWronskian`.
-/

namespace QuantumTheory.Transport

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
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hfs : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hx : 0 ≤ (‖z / 2‖ ^ 2) ^ n := by positivity
  calc
    ‖besselY1HarmonicTerm z n‖ =
        ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) *
          (‖z / 2‖ ^ 2) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
      have hnorm :
          ‖((((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) : ℂ))‖ =
            ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) := by
        calc
          ‖((((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)) : ℂ))‖ =
              ‖(harmonic n : ℝ) + (harmonic (n + 1) : ℝ)‖ := by
                simpa only [Complex.ofReal_add] using
                  (Complex.norm_real
                    ((harmonic n : ℝ) + (harmonic (n + 1) : ℝ)))
          _ = |(harmonic n : ℝ) + (harmonic (n + 1) : ℝ)| :=
            Real.norm_eq_abs _
          _ = _ := abs_of_nonneg hH.1
      simp only [besselY1HarmonicTerm, norm_div, norm_mul,
        norm_pow, norm_neg, hnorm, Complex.norm_natCast]
    _ ≤ (2 * ((n + 1).factorial : ℝ)) *
          (‖z / 2‖ ^ 2) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
      gcongr
      exact hH.2
    _ = 2 * ((‖z / 2‖ ^ 2) ^ n / (n.factorial : ℝ)) := by
      field_simp

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

/-- The leading power-series coefficient is H₀+H₁=1. -/
@[simp] theorem besselY1HarmonicTerm_zero (z : ℂ) :
    besselY1HarmonicTerm z 0 = 1 := by
  norm_num [besselY1HarmonicTerm, harmonic_succ, harmonic_zero]

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
  have hcancel :
      Complex.besselJ 0 z * z⁻¹ -
          Complex.besselJ 1 z * besselY0HarmonicCorrection z +
          (z / 4) * Complex.besselJ 0 z * besselY1HarmonicCorrection z = z⁻¹ := by
    apply (mul_left_cancel₀ hz)
    calc
      z * (Complex.besselJ 0 z * z⁻¹ -
          Complex.besselJ 1 z * besselY0HarmonicCorrection z +
          (z / 4) * Complex.besselJ 0 z * besselY1HarmonicCorrection z) =
          Complex.besselJ 0 z -
          z * Complex.besselJ 1 z * besselY0HarmonicCorrection z +
          (z ^ 2 / 4) * Complex.besselJ 0 z *
            besselY1HarmonicCorrection z := by
              field_simp [hz]
      _ = 1 := hidentity
      _ = z * z⁻¹ := by field_simp [hz]
  rw [hcancel]

end

end QuantumTheory.Transport
