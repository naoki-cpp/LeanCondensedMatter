import LeanCondensedMatter.Transport.Analysis.BesselCrossedXMoment
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
# Second-kind Bessel Y₀: harmonic-number power series

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
are separate proof obligations. In particular, merely defining Y₀
does not discharge `CrossedXBesselWronskian`.
-/

namespace QuantumTheory.Transport

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
        apply inv_le_one_of_one_le
        exact_mod_cast Nat.succ_pos n
      have hcast : (harmonic (n + 1) : ℝ) =
          (harmonic n : ℝ) + (((n + 1 : ℕ) : ℝ)⁻¹) := by
        rw [harmonic_succ]
        push_cast
        rfl
      rw [hcast]
      constructor
      · exact add_nonneg ih.1 hfrac
      · push_cast
        linarith [ih.2]

/-- Every harmonic number is bounded by the factorial of its index.
This is the basic domination needed for entire summability. -/
theorem harmonic_real_le_factorial (n : ℕ) :
    (harmonic n : ℝ) ≤ (n.factorial : ℝ) := by
  exact (harmonic_real_nonneg_le n).2.trans
    (by exact_mod_cast Nat.self_le_factorial n)

/-- The analytic correction coefficient appearing in the DLMF
order-zero second-kind Bessel series, with sign chosen so the Y₀
formula contains its subtraction. -/
noncomputable def besselY0HarmonicTerm (z : ℂ) (n : ℕ) : ℂ :=
  ((harmonic n : ℝ) : ℂ) * (-(z / 2) ^ 2) ^ n /
    ((n.factorial : ℂ) ^ 2)

/-- The absolute value of each harmonic correction term is dominated
by the factorial exponential term of argument `‖z/2‖²`. -/
theorem norm_besselY0HarmonicTerm_le_expTerm (z : ℂ) (n : ℕ) :
    ‖besselY0HarmonicTerm z n‖ ≤
      (‖z / 2‖ ^ 2) ^ n / (n.factorial : ℝ) := by
  have hH := harmonic_real_nonneg_le n
  have hHfac := harmonic_real_le_factorial n
  have hfpos : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hx : 0 ≤ (‖z / 2‖ ^ 2) ^ n := by positivity
  calc
    ‖besselY0HarmonicTerm z n‖ =
        (harmonic n : ℝ) * (‖z / 2‖ ^ 2) ^ n /
          (n.factorial : ℝ) ^ 2 := by
      simp only [besselY0HarmonicTerm, norm_div, norm_mul,
        norm_pow, norm_neg, Complex.norm_real,
        Complex.norm_natCast, Real.norm_eq_abs,
        abs_of_nonneg hH.1]
      ring
    _ ≤ (n.factorial : ℝ) * (‖z / 2‖ ^ 2) ^ n /
          (n.factorial : ℝ) ^ 2 := by
      gcongr
    _ = (‖z / 2‖ ^ 2) ^ n / (n.factorial : ℝ) := by
      field_simp

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

/-- The correction coefficients are zero at n=0, and the
first harmonic coefficient has its standard value H₁=1. -/
@[simp] theorem besselY0HarmonicTerm_zero (z : ℂ) :
    besselY0HarmonicTerm z 0 = 0 := by
  simp [besselY0HarmonicTerm, harmonic_zero]

@[simp] theorem besselY0HarmonicTerm_one (z : ℂ) :
    besselY0HarmonicTerm z 1 = -(z / 2) ^ 2 := by
  norm_num [besselY0HarmonicTerm, harmonic_succ, harmonic_zero]

end

end QuantumTheory.Transport
