import LeanCondensedMatter.Analysis.Fourier.PolarRadialKernels.Core
import LeanCondensedMatter.Analysis.Fourier.FullAngleCosineMoments
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Zeroth polar Fourier–Bessel kernel

The dimensionless full-angle kernel is expanded into exponential and cosine-moment
series, whose even coefficients identify the kernel with `2π J₀`.
This layer is independent of physical Fourier normalization, momentum measures,
and transport models, and depends on `PolarRadialKernels.Core`.
-/

namespace QuantumTheory

open AngularHarmonics
namespace Transport

open BesselHypergeometric

noncomputable section

open MeasureTheory
open scoped Interval

/-- Expand the radial Fourier phase in its exponential series and commute the
uniformly dominated series with integration over the finite angular interval.
This is the analytic step in the Fourier--Bessel integral representation. -/
theorem polarFourierZerothAngularKernel_eq_tsum_exp_integrals (z : ℝ) :
    polarFourierZerothAngularKernel z =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) ^ n /
          (Nat.factorial n : ℂ) := by
  let term : ℕ → ℝ → ℂ := fun n θ =>
    (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) ^ n /
      (Nat.factorial n : ℂ)
  have hbound (n : ℕ) (θ : ℝ) :
      ‖term n θ‖ ≤ |z| ^ n / (Nat.factorial n : ℝ) := by
    have hnorm :
        ‖Complex.I * (((z * Real.cos θ : ℝ) : ℂ))‖ ≤ |z| := by
      calc
        ‖Complex.I * (((z * Real.cos θ : ℝ) : ℂ))‖ =
            |z| * |Real.cos θ| := by
          simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
        _ ≤ |z| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg z)
        _ = |z| := by ring
    calc
      ‖term n θ‖ =
          ‖Complex.I * (((z * Real.cos θ : ℝ) : ℂ))‖ ^ n /
            (Nat.factorial n : ℝ) := by simp [term]
      _ ≤ |z| ^ n / (Nat.factorial n : ℝ) := by gcongr
  have hseries :
      HasSum
        (fun n : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi), term n θ)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := term) (f := polarFourierRadialPhase z)
      (bound := fun n (_ : ℝ) => |z| ^ n / (Nat.factorial n : ℝ))
    · intro n
      have hc : Continuous (term n) := by
        dsimp [term]
        fun_prop
      exact hc.aestronglyMeasurable
    · intro n
      filter_upwards [] with θ hθ
      exact hbound n θ
    · filter_upwards [] with θ hθ
      exact Real.summable_pow_div_factorial |z|
    · exact intervalIntegrable_const
    · filter_upwards [] with θ hθ
      change HasSum
        (fun n : ℕ =>
          (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) ^ n /
            (Nat.factorial n : ℂ))
        (Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))))
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
  simpa only [polarFourierZerothAngularKernel, term] using hseries.tsum_eq.symm

/-- Integral exponential coefficients are the corresponding real cosine moments,
multiplied by the scalar Fourier coefficient. -/
theorem polarFourierZerothAngularKernel_eq_tsum_moments (z : ℝ) :
    polarFourierZerothAngularKernel z =
      ∑' n : ℕ, (Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (fullAngleCosineMoment n : ℂ) := by
  rw [polarFourierZerothAngularKernel_eq_tsum_exp_integrals]
  congr 1
  funext n
  have hcos :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (((Real.cos θ : ℝ) : ℂ) ^ n)) =
        (fullAngleCosineMoment n : ℂ) := by
    simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal,
      fullAngleCosineMoment]
  have hterm (θ : ℝ) :
      (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) ^ n /
          (Nat.factorial n : ℂ) =
        ((Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ)) *
          (((Real.cos θ : ℝ) : ℂ) ^ n) := by
    have heq :
        Complex.I * (((z * Real.cos θ : ℝ) : ℂ)) =
          (Complex.I * (z : ℂ)) * ((Real.cos θ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, mul_pow]
    ring
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) ^ n /
          (Nat.factorial n : ℂ)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ)) *
          (((Real.cos θ : ℝ) : ℂ) ^ n) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact hterm θ
    _ = ((Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ)) *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (((Real.cos θ : ℝ) : ℂ) ^ n)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rw [hcos]

/-- The moment expansion of the full-angle Fourier kernel is absolutely summable. -/
theorem polarFourierZerothMoments_summable (z : ℝ) :
    Summable (fun n : ℕ =>
      (Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (fullAngleCosineMoment n : ℂ)) := by
  have hs := (Real.summable_pow_div_factorial |z|).mul_left (2 * Real.pi)
  apply Summable.of_norm_bounded hs
  intro n
  -- The cosine moment is bounded by the full period; the remaining factor is nonnegative.
  calc
    ‖(Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (fullAngleCosineMoment n : ℂ)‖ =
        (|z| ^ n / (Nat.factorial n : ℝ)) *
          ‖fullAngleCosineMoment n‖ := by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_I,
        Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
        one_mul]
    _ ≤ (|z| ^ n / (Nat.factorial n : ℝ)) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (fullAngleCosineMoment_norm_le n)
        (div_nonneg (pow_nonneg (abs_nonneg z) _) (by positivity))
    _ = (2 * Real.pi) * (|z| ^ n / (Nat.factorial n : ℝ)) := by ring

/-- The coefficient of each even Fourier moment agrees with the corresponding
coefficient in the zeroth Bessel series. -/
theorem polarFourierZerothMoment_even_eq_bessel (z : ℝ) (n : ℕ) :
    (Complex.I * (z : ℂ)) ^ (2 * n) / (Nat.factorial (2 * n) : ℂ) *
      (fullAngleCosineMoment (2 * n) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
          (-((z : ℂ) / 2) ^ 2) ^ n) := by
  have hcoeff := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 n
  norm_num only [Nat.add_zero] at hcoeff
  rw [fullAngleCosineMoment_even_factorial, hcoeff, ← pow_two]
  push_cast
  have hI : (Complex.I * (z : ℂ)) ^ (2 * n) = (-(z : ℂ) ^ 2) ^ n := by
    rw [pow_mul, mul_pow, Complex.I_sq]
    ring
  have hdiv : (-((z : ℂ) / 2) ^ 2) ^ n =
      (-(z : ℂ) ^ 2) ^ n / (4 : ℂ) ^ n := by
    rw [← div_pow]
    congr 1
    ring
  rw [hI, hdiv]
  have hfac : (Nat.factorial (2 * n) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hfacn : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfour : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- The full-angle zeroth Fourier kernel is exactly \(2π J₀\), with Mathlib's Bessel
function and no restriction on the real radial argument. -/
theorem polarFourierZerothAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierZerothAngularKernel z =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 (z : ℂ) := by
  let f : ℕ → ℂ := fun n =>
    (Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
      (fullAngleCosineMoment n : ℂ)
  have hf : Summable f := polarFourierZerothMoments_summable z
  have he : Summable (fun n : ℕ => f (2 * n)) :=
    hf.comp_injective (by intro a b hab; omega)
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hf.comp_injective (by
      intro a b hab
      change 2 * a + 1 = 2 * b + 1 at hab
      omega)
  have hodd (n : ℕ) : f (2 * n + 1) = 0 := by
    simp [f]
  calc
    polarFourierZerothAngularKernel z = ∑' n : ℕ, f n := by
      exact polarFourierZerothAngularKernel_eq_tsum_moments z
    _ = (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) :=
      (tsum_even_add_odd he ho).symm
    _ = ∑' n : ℕ, f (2 * n) := by
      simp only [hodd, tsum_zero, add_zero]
    _ = ∑' n : ℕ, ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
          (-((z : ℂ) / 2) ^ 2) ^ n) := by
      apply tsum_congr
      intro n
      exact polarFourierZerothMoment_even_eq_bessel z n
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
          (-((z : ℂ) / 2) ^ 2) ^ n) := by
      rw [tsum_mul_left]
    _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 (z : ℂ) := by
      rw [besselJZero_eq_regularizedHGTsum]

end
end Transport
end QuantumTheory
