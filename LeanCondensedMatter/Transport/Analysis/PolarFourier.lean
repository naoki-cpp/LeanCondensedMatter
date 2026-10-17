import LeanCondensedMatter.Transport.Analysis.AngularHarmonics
import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional polar Fourier transform

This module owns the representation-independent scalar Fourier transform used when a two-dimensional
physical-momentum integral is written in polar coordinates with a finite radial cutoff. The transform
includes the physical continuum normalization `d²p / (2πℏ)²` and the polar Jacobian `p`, while the
consumer supplies the momentum-space scalar field. The Cartesian Fourier phase itself is inherited
from the dimension-independent `Analysis.FourierGeometry` layer; this module owns only its
two-dimensional polar specialization and angular reduction.

The full-angle kernels below are the canonical intermediate for radial Fourier reduction. Constant,
first, and second angular channels are supplied through `AngularHarmonicCoefficients`, shared with
ordinary angular integration. The kernels remain explicit finite interval integrals rather than being identified with
Bessel functions. Mathlib v4.35.0 provides `Complex.besselJ` and parity/analyticity results, but
not yet the angular integral representations required to prove those identifications.

No model Hamiltonian, matrix representation, disorder approximation, real-space cutoff, or
conductivity normalization is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Two-dimensional polar point `(ρ cos φ, ρ sin φ)`. -/
def polarPoint2D (radius angle : ℝ) : Fin 2 → ℝ :=
  ![radius * Real.cos angle, radius * Real.sin angle]

/-- The two-dimensional polar point is the generic finite-dimensional radial scaling specialized to
its usual unit direction `(cos φ, sin φ)`. -/
theorem polarPoint2D_eq_radialPoint (radius angle : ℝ) :
    polarPoint2D radius angle =
      radialPoint radius ![Real.cos angle, Real.sin angle] := by
  funext i
  fin_cases i <;> simp [polarPoint2D, radialPoint]

/-- Negating the radius negates a two-dimensional polar point at fixed angle. -/
theorem neg_polarPoint2D (radius angle : ℝ) :
    -(polarPoint2D radius angle) = polarPoint2D (-radius) angle := by
  rw [polarPoint2D_eq_radialPoint, polarPoint2D_eq_radialPoint,
    radialPoint_neg_radius]

/-- Fourier phase `exp(i p·r / ℏ)` for polar momentum `(p cos θ, p sin θ)` in two dimensions. -/
def physicalMomentumPolarFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  physicalMomentumFourierPhase hbar (polarPoint2D p θ) r

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- The physical polar Fourier phase at a polar real-space point depends only on the angular
difference `θ - φ`. -/
theorem physicalMomentumPolarFourierPhase_polarPoint2D
    (hbar p θ radius angle : ℝ) :
    physicalMomentumPolarFourierPhase hbar p θ (polarPoint2D radius angle) =
      polarFourierRadialPhase (p * radius / hbar) (θ - angle) := by
  unfold physicalMomentumPolarFourierPhase physicalMomentumFourierPhase polarFourierRadialPhase
  simp only [polarPoint2D, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.cos_sub]
  apply congrArg Complex.exp
  push_cast
  ring_nf

/-- Zeroth full-angle radial Fourier kernel. A future integral-representation theorem should
identify it with `2π J₀(z)` using Mathlib's `Complex.besselJ`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel. A future integral-representation theorem should
identify it with `2π i J₁(z)` using Mathlib's `Complex.besselJ`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  have h := integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi)
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using h
/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)` polynomial needed by
quadratic angular products. A future integral-representation theorem should identify it with
`-2π J₂(z)` using Mathlib's `Complex.besselJ`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

/-- The real cosine moment over a full polar revolution. Its explicit even moments
are the coefficients in the Fourier--Bessel expansion of the zeroth kernel. -/
noncomputable def polarFourierCosineMoment (n : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ n

@[simp] theorem polarFourierCosineMoment_zero :
    polarFourierCosineMoment 0 = 2 * Real.pi := by
  simp [polarFourierCosineMoment]

@[simp] theorem polarFourierCosineMoment_one :
    polarFourierCosineMoment 1 = 0 := by
  simp [polarFourierCosineMoment]

/-- The full-period cosine moments satisfy the standard reduction formula. -/
theorem polarFourierCosineMoment_add_two (n : ℕ) :
    polarFourierCosineMoment (n + 2) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * polarFourierCosineMoment n := by
  simpa [polarFourierCosineMoment] using
    (integral_cos_pow (a := (0 : ℝ)) (b := 2 * Real.pi) n)

/-- Closed finite-product formula for every even full-angle cosine moment. -/
theorem polarFourierCosineMoment_even (n : ℕ) :
    polarFourierCosineMoment (2 * n) =
      (2 * Real.pi) *
        ∏ k ∈ Finset.range n, ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hindex : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hindex, polarFourierCosineMoment_add_two, ih, Finset.prod_range_succ]
      push_cast
      ring

/-- The even full-angle cosine moment in factorial form, ready for the
coefficient comparison with Mathlib's regularized hypergeometric Bessel series. -/
theorem polarFourierCosineMoment_even_factorial (n : ℕ) :
    polarFourierCosineMoment (2 * n) =
      (2 * Real.pi) * (Nat.factorial (2 * n) : ℝ) / ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
  rw [polarFourierCosineMoment_even]
  have hprod (n : ℕ) :
      (∏ k ∈ Finset.range n, ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2))) =
        (Nat.factorial (2 * n) : ℝ) / ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) ^ 2) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hfac2 :
            (Nat.factorial (2 * (n + 1)) : ℝ) =
              (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (Nat.factorial (2 * n) : ℝ) := by
          have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
          rw [hindex, Nat.factorial_succ, Nat.factorial_succ]
          push_cast
          ring
        have hfacn : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [Finset.prod_range_succ, ih, hfac2, hfacn, pow_succ]
        have hfact : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hpow : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
        have hden : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
        have hsucc : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hfact, hpow, hden, hsucc]
        ring
  rw [hprod]
  ring

/-- Every odd full-angle cosine moment vanishes. -/
@[simp] theorem polarFourierCosineMoment_odd (n : ℕ) :
    polarFourierCosineMoment (2 * n + 1) = 0 := by
  induction n with
  | zero => simpa using polarFourierCosineMoment_one
  | succ n ih =>
      have hindex : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hindex, polarFourierCosineMoment_add_two, ih, mul_zero]

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
        (polarFourierCosineMoment n : ℂ) := by
  rw [polarFourierZerothAngularKernel_eq_tsum_exp_integrals]
  congr 1
  funext n
  have hcos :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (((Real.cos θ : ℝ) : ℂ) ^ n)) =
        (polarFourierCosineMoment n : ℂ) := by
    simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal,
      polarFourierCosineMoment]
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

/-- The zeroth-order regularized hypergeometric coefficient of Mathlib's Bessel function
is a reciprocal square of a factorial. -/
theorem polarFourierBesselZeroCoeff (n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n =
      1 / (Nat.factorial n : ℂ) ^ 2 := by
  have hgamma : Complex.Gamma ((1 : ℂ) + (n : ℂ)) =
      (Nat.factorial n : ℂ) := by
    simpa only [add_comm] using Complex.Gamma_nat_eq_factorial n
  simp [Complex.regularizedHGFunCoeff, hgamma, pow_two]

/-- A full-period cosine moment is bounded by the length of its integration interval. -/
theorem polarFourierCosineMoment_norm_le (n : ℕ) :
    ‖polarFourierCosineMoment n‖ ≤ 2 * Real.pi := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (C := (1 : ℝ))
    (f := fun θ : ℝ => Real.cos θ ^ n) (by
      intro θ _
      simp only [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ))
  simpa only [polarFourierCosineMoment, one_mul, sub_zero,
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le)]
    using h

/-- The moment expansion of the full-angle Fourier kernel is absolutely summable. -/
theorem polarFourierZerothMoments_summable (z : ℝ) :
    Summable (fun n : ℕ =>
      (Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (polarFourierCosineMoment n : ℂ)) := by
  have hs := (Real.summable_pow_div_factorial |z|).mul_left (2 * Real.pi)
  apply Summable.of_norm_bounded hs
  intro n
  have hfact : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ |z| ^ n := pow_nonneg (abs_nonneg z) _
  have hmoment := polarFourierCosineMoment_norm_le n
  calc
    ‖(Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (polarFourierCosineMoment n : ℂ)‖ =
        (|z| ^ n / (Nat.factorial n : ℝ)) *
          ‖polarFourierCosineMoment n‖ := by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_I,
        Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
        one_mul]
    _ ≤ (|z| ^ n / (Nat.factorial n : ℝ)) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hmoment (div_nonneg hpow hfact)
    _ = (2 * Real.pi) * (|z| ^ n / (Nat.factorial n : ℝ)) := by ring

/-- Mathlib's integer-order Bessel function has the expected coefficient expansion. -/
theorem polarFourierBesselJZero_eq_tsum (z : ℂ) :
    Complex.besselJ 0 z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
        (-(z / 2) ^ 2) ^ n := by
  change (z / 2) ^ (0 : ℂ) *
      Complex.regularizedHGFun 0 {(1 : ℂ)} (-(z / 2) ^ 2) = _
  rw [Complex.cpow_zero, one_mul]
  change (Complex.regularizedHGFunSeries 0 {(1 : ℂ)}).sum (-(z / 2) ^ 2) = _
  rw [Complex.regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- The coefficient of each even Fourier moment agrees with the corresponding
coefficient in the zeroth Bessel series. -/
theorem polarFourierZerothMoment_even_eq_bessel (z : ℝ) (n : ℕ) :
    (Complex.I * (z : ℂ)) ^ (2 * n) / (Nat.factorial (2 * n) : ℂ) *
      (polarFourierCosineMoment (2 * n) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) *
        (Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
          (-((z : ℂ) / 2) ^ 2) ^ n) := by
  rw [polarFourierCosineMoment_even_factorial, polarFourierBesselZeroCoeff]
  push_cast
  have hI : (Complex.I * (z : ℂ)) ^ (2 * n) = (-(z : ℂ) ^ 2) ^ n := by
    rw [pow_mul, mul_pow, Complex.I_sq]
    ring
  have hdiv : (-((z : ℂ) / 2) ^ 2) ^ n =
      (-(z : ℂ) ^ 2) ^ n / (4 : ℂ) ^ n := by
    congr 1
    ring
  rw [hI, hdiv]
  have hfac : (Nat.factorial (2 * n) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hfacn : (Nat.factorial n : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfour : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- The full-angle zeroth Fourier kernel is exactly \(2π J₀\), with Mathlib's Bessel
function and no restriction on the real radial argument. -/
theorem polarFourierZerothAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierZerothAngularKernel z =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 (z : ℂ) := by
  let f : ℕ → ℂ := fun n =>
    (Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
      (polarFourierCosineMoment n : ℂ)
  have hf : Summable f := polarFourierZerothMoments_summable z
  have he : Summable (fun n : ℕ => f (2 * n)) :=
    hf.comp_injective (by intro a b hab; omega)
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hf.comp_injective (by intro a b hab; omega)
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
      rw [polarFourierBesselJZero_eq_tsum]

/-- The zeroth radial Fourier kernel is normalized by the full polar angle at the origin. -/
@[simp] theorem polarFourierZerothAngularKernel_zero :
    polarFourierZerothAngularKernel 0 = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [polarFourierZerothAngularKernel, polarFourierRadialPhase]

@[fun_prop]
theorem continuous_polarFourierZerothAngularKernel :
    Continuous polarFourierZerothAngularKernel := by
  unfold polarFourierZerothAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierFirstCosineAngularKernel :
    Continuous polarFourierFirstCosineAngularKernel := by
  unfold polarFourierFirstCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

@[fun_prop]
theorem continuous_polarFourierSecondCosineAngularKernel :
    Continuous polarFourierSecondCosineAngularKernel := by
  unfold polarFourierSecondCosineAngularKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry polarFourierRadialPhase
  fun_prop

/-- The Fourier phase has unit norm for every real argument. -/
private theorem norm_polarFourierRadialPhase (z θ : ℝ) :
    ‖polarFourierRadialPhase z θ‖ = 1 := by
  simp [polarFourierRadialPhase, Complex.norm_exp, Complex.mul_re]

/-- The first nonzero-argument differential relation of the radial Fourier
harmonics: the derivative of the zeroth angular kernel is `i` times the
first-cosine kernel.

Unlike an origin-only normalization, this identity holds for all real
Fourier arguments and is a step toward identifying the Fourier kernels
with the integer-order Bessel functions in Mathlib v4.35.0. -/
theorem polarFourierZerothAngularKernel_hasDerivAt (z : ℝ) :
    HasDerivAt polarFourierZerothAngularKernel
      (Complex.I * polarFourierFirstCosineAngularKernel z) z := by
  let derivative : ℝ → ℝ → ℂ := fun x θ =>
    Complex.I * (((Real.cos θ : ℝ) : ℂ)) * polarFourierRadialPhase x θ
  have hdiff (x θ : ℝ) :
      HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ)
        (derivative x θ) x := by
    have hmul : HasDerivAt (fun t : ℝ => t * Real.cos θ)
        (Real.cos θ) x := by
      simpa using (hasDerivAt_id x).mul_const (Real.cos θ)
    have harg : HasDerivAt
        (fun t : ℝ => Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
        (Complex.I * (((Real.cos θ : ℝ) : ℂ))) x :=
      hmul.ofReal_comp |>.const_mul Complex.I
    have h := (Complex.hasDerivAt_exp _).comp x harg
    convert h using 1
    · rfl
    · dsimp [derivative, polarFourierRadialPhase]
      ring
  have hcont (x : ℝ) :
      Continuous (fun θ : ℝ => polarFourierRadialPhase x θ) := by
    dsimp [polarFourierRadialPhase]
    fun_prop
  have hcont' (x : ℝ) : Continuous (derivative x) := by
    dsimp [derivative]
    fun_prop
  have hbound (x θ : ℝ) : ‖derivative x θ‖ ≤ (1 : ℝ) := by
    have hcos := Real.abs_cos_le_one θ
    simpa only [derivative, norm_mul, norm_polarFourierRadialPhase,
      Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, mul_one] using hcos
  have hmain :
      HasDerivAt
        (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
          polarFourierRadialPhase x θ)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) z := by
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x θ => polarFourierRadialPhase x θ)
      (F' := derivative)
      (bound := fun _θ : ℝ => (1 : ℝ))
      (s := Set.univ) (x₀ := z) (a := (0 : ℝ)) (b := 2 * Real.pi)
      Filter.univ_mem
      (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
      ((hcont z).intervalIntegrable _ _)
      ((hcont' z).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun θ _ x _ => hbound x θ)
      (intervalIntegrable_const)
      (Filter.Eventually.of_forall fun θ _ x _ => hdiff x θ)).2
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) =
        Complex.I * polarFourierFirstCosineAngularKernel z := by
    unfold polarFourierFirstCosineAngularKernel
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [derivative]
    ring
  change HasDerivAt
    (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase x θ)
    (Complex.I * polarFourierFirstCosineAngularKernel z) z
  rw [← hrew]
  exact hmain

/-- Derivative of the dimensionless radial Fourier phase with respect to the polar angle. -/
private theorem polarFourierRadialPhase_hasDerivAt (z θ : ℝ) :
    HasDerivAt (polarFourierRadialPhase z)
      ((-Complex.I * (z : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
        polarFourierRadialPhase z θ) θ := by
  have hcos : HasDerivAt (fun t : ℝ => ((z * Real.cos t : ℝ) : ℂ))
      ((-z * Real.sin θ : ℝ) : ℂ) θ := by
    simpa using ((Real.hasDerivAt_cos θ).const_mul z).ofReal_comp
  have harg : HasDerivAt
      (fun t : ℝ => Complex.I * ((z * Real.cos t : ℝ) : ℂ))
      (Complex.I * ((-z * Real.sin θ : ℝ) : ℂ)) θ :=
    hcos.const_mul Complex.I
  have hphase := (Complex.hasDerivAt_exp _).comp θ harg
  convert hphase using 1
  · rfl
  · simp [polarFourierRadialPhase]
    ring

/-- Angular integration by parts: the first Fourier harmonic is constrained by the
zeroth and second harmonics without assuming nonzero radial argument.

With the unnormalized kernels used by the physical Fourier measure, this is
`2 K1(z) = i z (K0(z) - K2(z))`. In Bessel notation this is the
`J0 + J2 = 2 J1/z` recurrence, stated without division by `z`. -/
theorem polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second (z : ℝ) :
    2 * polarFourierFirstCosineAngularKernel z =
      Complex.I * (z : ℂ) *
        (polarFourierZerothAngularKernel z - polarFourierSecondCosineAngularKernel z) := by
  let phase : ℝ → ℂ := polarFourierRadialPhase z
  let sine : ℝ → ℂ := fun θ => ((Real.sin θ : ℝ) : ℂ)
  let cosine : ℝ → ℂ := fun θ => ((Real.cos θ : ℝ) : ℂ)
  have hcphase : Continuous phase := by
    change Continuous (fun θ : ℝ =>
      Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))))
    fun_prop
  have hcsin : Continuous sine := by
    dsimp [sine]
    fun_prop
  have hccos : Continuous cosine := by
    dsimp [cosine]
    fun_prop
  have hcvprime : Continuous
      (fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ) :=
    ((continuous_const.mul hcsin).mul hcphase)
  have hsin : ∀ θ : ℝ, HasDerivAt sine (cosine θ) θ := by
    intro θ
    simpa [sine, cosine] using (Real.hasDerivAt_sin θ).ofReal_comp
  have hphase : ∀ θ : ℝ, HasDerivAt phase
      ((-Complex.I * (z : ℂ) * sine θ) * phase θ) θ := by
    intro θ
    exact polarFourierRadialPhase_hasDerivAt z θ
  have hzero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ +
          sine θ * ((-Complex.I * (z : ℂ) * sine θ) * phase θ)) = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (u := sine) (v := phase) (u' := cosine)
      (v' := fun θ => (-Complex.I * (z : ℂ) * sine θ) * phase θ)
      (fun θ _ => hsin θ) (fun θ _ => hphase θ)
      (hccos.intervalIntegrable _ _)
      (hcvprime.intervalIntegrable _ _)
    simpa [sine, cosine] using h
  have hcosInt : IntervalIntegrable (fun θ : ℝ => cosine θ * phase θ)
      volume 0 (2 * Real.pi) := by
    exact (hccos.mul hcphase).intervalIntegrable _ _
  have hsinSqInt : IntervalIntegrable
      (fun θ : ℝ => phase θ * sine θ ^ 2) volume 0 (2 * Real.pi) := by
    exact (hcphase.mul (hcsin.pow 2)).intervalIntegrable _ _
  have hfirst :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), cosine θ * phase θ) =
        (Complex.I * (z : ℂ)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) := by
    have h' : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        cosine θ * phase θ -
          (Complex.I * (z : ℂ)) * (phase θ * sine θ ^ 2)) = 0 := by
      convert hzero using 1
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    rw [intervalIntegral.integral_sub hcosInt (hsinSqInt.const_mul _),
      intervalIntegral.integral_const_mul, sub_eq_zero] at h'
    exact h'
  have htrig (θ : ℝ) :
      2 * (phase θ * sine θ ^ 2) =
        phase θ -
          phase θ * (cosine θ ^ 2 - sine θ ^ 2) := by
    have h : sine θ ^ 2 + cosine θ ^ 2 = 1 := by
      change (((Real.sin θ : ℝ) : ℂ) ^ 2) + (((Real.cos θ : ℝ) : ℂ) ^ 2) = 1
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    linear_combination (phase θ) * h
  have hsecond :
      2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) =
        polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z := by
    calc
      2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            2 * (phase θ * sine θ ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
            phase θ - phase θ * (cosine θ ^ 2 - sine θ ^ 2) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact htrig θ
      _ = polarFourierZerothAngularKernel z -
            polarFourierSecondCosineAngularKernel z := by
        rw [intervalIntegral.integral_sub]
        · rfl
        · exact hcphase.intervalIntegrable _ _
        · exact (hcphase.mul ((hccos.pow 2).sub (hcsin.pow 2))).intervalIntegrable _ _
  have hfirstKernel :
      polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2) := by
    rw [polarFourierFirstCosineAngularKernel]
    convert hfirst using 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [cosine, phase, mul_comm]
  calc
    2 * polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2)) := by
      rw [hfirstKernel]
      ring
    _ = _ := by rw [hsecond]

/-- The unnormalized first-harmonic recurrence also holds after finite radial
momentum integration. This reduces any weighted K1 moment to K0/K2 moments
with one additional radial power, without division by the Fourier argument,
a regulator limit, or any assumption on the weight. -/
theorem integral_polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
    (hbar pMax radius : ℝ) (f : ℝ → ℂ) :
    2 * (∫ p in (0 : ℝ)..pMax,
      (p : ℂ) *
        (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
      Complex.I * (((radius / hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) ^ 2 *
            ((polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p) := by
  calc
    2 * (∫ p in (0 : ℝ)..pMax,
        (p : ℂ) *
          (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
        ∫ p in (0 : ℝ)..pMax,
          (2 : ℂ) * ((p : ℂ) *
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ p in (0 : ℝ)..pMax,
          (Complex.I * (((radius / hbar : ℝ) : ℂ))) *
            ((p : ℂ) ^ 2 *
              ((polarFourierZerothAngularKernel (p * radius / hbar) -
                  polarFourierSecondCosineAngularKernel (p * radius / hbar)) * f p)) := by
      apply intervalIntegral.integral_congr
      intro p _
      have hrec :=
        polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second
          (p * radius / hbar)
      have hp : ((p * radius / hbar : ℝ) : ℂ) =
          (p : ℂ) * (((radius / hbar : ℝ) : ℂ)) := by
        calc
          ((p * radius / hbar : ℝ) : ℂ) =
              ((p * (radius / hbar) : ℝ) : ℂ) := by
            congr 1
            ring
          _ = (p : ℂ) * (((radius / hbar : ℝ) : ℂ)) := by push_cast; rfl
      rw [hp] at hrec
      calc
        (2 : ℂ) * ((p : ℂ) *
            (polarFourierFirstCosineAngularKernel (p * radius / hbar) * f p)) =
          (p : ℂ) *
            (2 * polarFourierFirstCosineAngularKernel (p * radius / hbar)) * f p := by
            ring
        _ = (p : ℂ) *
            (Complex.I * ((p : ℂ) * (((radius / hbar : ℝ) : ℂ))) *
              (polarFourierZerothAngularKernel (p * radius / hbar) -
                polarFourierSecondCosineAngularKernel (p * radius / hbar))) * f p := by
            rw [hrec]
        _ = _ := by ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hneg :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            unfold f polarFourierRadialPhase
            dsimp
            rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
            push_cast
            ring
      _ = -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
        rw [intervalIntegral.integral_neg]
  have hself :
      -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
    hneg.symm.trans hsub
  have hz : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 :=
    CharZero.neg_eq_self_iff.mp hself
  simpa [f] using hz

/-- The mixed quadratic harmonic `cos θ sin θ` vanishes against the radial Fourier phase over one
full angle. -/
theorem integral_polarFourierRadialPhase_mul_cos_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ *
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) = 0 := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ *
      (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hneg :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    calc
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), -f θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            unfold f polarFourierRadialPhase
            dsimp
            rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
            push_cast
            ring
      _ = -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
        rw [intervalIntegral.integral_neg]
  have hself :
      -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
    hneg.symm.trans hsub
  have hz : (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 :=
    CharZero.neg_eq_self_iff.mp hself
  simpa [f] using hz

/-- Phase-weighted full-angle integration of the canonical constant/first/second harmonic
decomposition. The first-sine and mixed-second channels vanish on the radial axis. -/
theorem AngularHarmonicCoefficients.integral_polarFourierRadialPhase
    (coefficients : AngularHarmonicCoefficients ℂ) (z p : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
  have hphase : Continuous fun θ : ℝ => polarFourierRadialPhase z θ := by
    unfold polarFourierRadialPhase
    fun_prop
  have hcos : Continuous fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ) := by
    fun_prop
  have hsin : Continuous fun θ : ℝ => ((Real.sin θ : ℝ) : ℂ) := by
    fun_prop
  have hA : IntervalIntegrable
      (fun θ : ℝ => polarFourierRadialPhase z θ * coefficients.constant)
      volume 0 (2 * Real.pi) :=
    (hphase.mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hB : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) * coefficients.firstCosine)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hcos).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hC : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) * coefficients.firstSine)
      volume 0 (2 * Real.pi) :=
    ((hphase.mul hsin).mul continuous_const).intervalIntegrable 0 (2 * Real.pi)
  have hD : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ *
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))) *
            coefficients.secondCosine) volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hE : IntervalIntegrable
      (fun θ : ℝ =>
        (polarFourierRadialPhase z θ *
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) * coefficients.secondMixed)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
        (p : ℂ) *
          ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
            polarFourierRadialPhase z θ * coefficients.constant +
              (polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)) *
                coefficients.firstCosine +
              (polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) *
                coefficients.firstSine +
              (polarFourierRadialPhase z θ *
                ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))) *
                coefficients.secondCosine +
              (polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) *
                coefficients.secondMixed := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          simp only [AngularHarmonicCoefficients.eval, smul_eq_mul]
          ring
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
      rw [intervalIntegral.integral_add (((hA.add hB).add hC).add hD) hE,
        intervalIntegral.integral_add ((hA.add hB).add hC) hD,
        intervalIntegral.integral_add (hA.add hB) hC,
        intervalIntegral.integral_add hA hB,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        integral_polarFourierRadialPhase_mul_sin_zero,
        integral_polarFourierRadialPhase_mul_cos_mul_sin_zero]
      simp [polarFourierZerothAngularKernel, polarFourierFirstCosineAngularKernel,
        polarFourierSecondCosineAngularKernel]

/-- Full-angle reduction for a scalar field containing only constant and first sine/cosine
harmonics. The sine harmonic drops out on the radial axis, leaving the zeroth and first-cosine
kernels that later become the `J₀` and `J₁` channels. -/
theorem integral_polarFourierRadialPhase_first_harmonics
    (z p : ℝ) (a b c : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z * b) := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := a
      firstCosine := b
      firstSine := c
      secondCosine := 0
      secondMixed := 0 }
  simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
    coefficients.integral_polarFourierRadialPhase z p

private theorem intervalIntegral_fullPeriod_comp_sub_eq
    (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h := hf.intervalIntegral_add_eq (-angle) 0
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

/-- Reversing the radial Fourier argument is equivalent to shifting the polar angle by π. -/
private theorem polarFourierRadialPhase_neg_eq_shift_pi (z θ : ℝ) :
    polarFourierRadialPhase (-z) θ =
      polarFourierRadialPhase z (θ - Real.pi) := by
  unfold polarFourierRadialPhase
  apply congrArg Complex.exp
  rw [Real.cos_sub_pi]
  push_cast
  ring

/-- The zeroth full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierZerothAngularKernel_neg (z : ℝ) :
    polarFourierZerothAngularKernel (-z) =
      polarFourierZerothAngularKernel z := by
  let f : ℝ → ℂ := fun θ => polarFourierRadialPhase z θ
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi]
  unfold polarFourierZerothAngularKernel
  simp_rw [polarFourierRadialPhase_neg_eq_shift_pi]
  simpa [f] using intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi

/-- The first-cosine full-angle radial Fourier kernel is odd in its radial argument. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_neg (z : ℝ) :
    polarFourierFirstCosineAngularKernel (-z) =
      -polarFourierFirstCosineAngularKernel z := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi]
  have hpoint (θ : ℝ) :
      polarFourierRadialPhase (-z) θ * ((Real.cos θ : ℝ) : ℂ) =
        -f (θ - Real.pi) := by
    rw [polarFourierRadialPhase_neg_eq_shift_pi]
    dsimp [f]
    rw [Real.cos_sub_pi]
    push_cast
    ring
  unfold polarFourierFirstCosineAngularKernel
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg,
    intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi]

/-- The second-cosine full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_neg (z : ℝ) :
    polarFourierSecondCosineAngularKernel (-z) =
      polarFourierSecondCosineAngularKernel z := by
  let f : ℝ → ℂ := fun θ =>
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    unfold polarFourierRadialPhase
    rw [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hpoint (θ : ℝ) :
      polarFourierRadialPhase (-z) θ *
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) =
        f (θ - Real.pi) := by
    rw [polarFourierRadialPhase_neg_eq_shift_pi]
    dsimp [f]
    rw [Real.cos_sub_pi, Real.sin_sub_pi]
    push_cast
    ring
  unfold polarFourierSecondCosineAngularKernel
  simp_rw [hpoint]
  simpa [f] using intervalIntegral_fullPeriod_comp_sub_eq f hf Real.pi

/-- Complex conjugation of the angular Fourier phase reverses its radial argument. -/
private theorem polarFourierRadialPhase_conj (z θ : ℝ) :
    conj (polarFourierRadialPhase z θ) =
      polarFourierRadialPhase (-z) θ := by
  unfold polarFourierRadialPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Complex conjugation commutes with full-angle integration. -/
private theorem integral_polarFourier_conj (f : ℝ → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (f θ)) =
      conj (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) := by
  simpa using (Complex.conjLIE.toLinearIsometry).intervalIntegral_comp_comm
    (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi)

/-- The zeroth angular Fourier kernel is real for real radial arguments. -/
@[simp] theorem polarFourierZerothAngularKernel_conj (z : ℝ) :
    conj (polarFourierZerothAngularKernel z) =
      polarFourierZerothAngularKernel z := by
  calc
    conj (polarFourierZerothAngularKernel z) =
        polarFourierZerothAngularKernel (-z) := by
      unfold polarFourierZerothAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      exact polarFourierRadialPhase_conj z θ
    _ = polarFourierZerothAngularKernel z := polarFourierZerothAngularKernel_neg z

/-- The first cosine angular Fourier kernel is purely imaginary for real radial arguments. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_conj (z : ℝ) :
    conj (polarFourierFirstCosineAngularKernel z) =
      -polarFourierFirstCosineAngularKernel z := by
  calc
    conj (polarFourierFirstCosineAngularKernel z) =
        polarFourierFirstCosineAngularKernel (-z) := by
      unfold polarFourierFirstCosineAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [map_mul, Complex.conj_ofReal, polarFourierRadialPhase_conj]
    _ = -polarFourierFirstCosineAngularKernel z := polarFourierFirstCosineAngularKernel_neg z

/-- The second cosine angular Fourier kernel is real for real radial arguments. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_conj (z : ℝ) :
    conj (polarFourierSecondCosineAngularKernel z) =
      polarFourierSecondCosineAngularKernel z := by
  calc
    conj (polarFourierSecondCosineAngularKernel z) =
        polarFourierSecondCosineAngularKernel (-z) := by
      unfold polarFourierSecondCosineAngularKernel
      rw [← integral_polarFourier_conj]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal,
        polarFourierRadialPhase_conj]
    _ = polarFourierSecondCosineAngularKernel z := polarFourierSecondCosineAngularKernel_neg z

private theorem angular_second_harmonics_add
    (angle θ : ℝ) (a b c d e : ℂ) :
    a + ((Real.cos (θ + angle) : ℝ) : ℂ) * b +
          ((Real.sin (θ + angle) : ℝ) : ℂ) * c +
          ((((Real.cos (θ + angle) : ℝ) : ℂ) ^ 2) -
            (((Real.sin (θ + angle) : ℝ) : ℂ) ^ 2)) * d +
          (((Real.cos (θ + angle) : ℝ) : ℂ) *
            ((Real.sin (θ + angle) : ℝ) : ℂ)) * e =
      a + ((Real.cos θ : ℝ) : ℂ) *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          ((Real.sin θ : ℝ) : ℂ) *
            (-((Real.sin angle : ℝ) : ℂ) * b + ((Real.cos angle : ℝ) : ℂ) * c) +
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e) +
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) *
            ((-4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ))) * d +
              (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * e)) := by
  rw [Real.cos_add, Real.sin_add]
  push_cast
  ring

private theorem integral_polarFourierRadialPhase_shifted_second_harmonics
    (z p angle : ℝ) (a b c d e : ℂ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
        (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
          ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
          (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
  let f : ℝ → ℂ := fun α =>
    ((p : ℂ) * polarFourierRadialPhase z α) *
      (a + ((Real.cos (α + angle) : ℝ) : ℂ) * b +
        ((Real.sin (α + angle) : ℝ) : ℂ) * c +
        ((((Real.cos (α + angle) : ℝ) : ℂ) ^ 2) -
          (((Real.sin (α + angle) : ℝ) : ℂ) ^ 2)) * d +
        (((Real.cos (α + angle) : ℝ) : ℂ) *
          ((Real.sin (α + angle) : ℝ) : ℂ)) * e)
  have hf : Function.Periodic f (2 * Real.pi) := by
    intro α
    simp only [f, polarFourierRadialPhase]
    rw [Real.cos_add_two_pi]
    have hangle : α + 2 * Real.pi + angle = (α + angle) + 2 * Real.pi := by
      ring
    rw [hangle, Real.cos_add_two_pi, Real.sin_add_two_pi]
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) *
          (a + ((Real.cos θ : ℝ) : ℂ) * b + ((Real.sin θ : ℝ) : ℂ) * c +
            ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2)) * d +
            (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)) * e)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle) := by
          apply intervalIntegral.integral_congr
          intro θ _
          simp [f]
    _ = ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ :=
      intervalIntegral_fullPeriod_comp_sub_eq f hf angle
    _ = (p : ℂ) *
        (polarFourierZerothAngularKernel z * a +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * d +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * e)) := by
      simp_rw [f, angular_second_harmonics_add]
      let coefficients : AngularHarmonicCoefficients ℂ :=
        { constant := a
          firstCosine :=
            ((Real.cos angle : ℝ) : ℂ) * b + ((Real.sin angle : ℝ) : ℂ) * c
          firstSine :=
            -((Real.sin angle : ℝ) : ℂ) * b + ((Real.cos angle : ℝ) : ℂ) * c
          secondCosine :=
            (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * d +
              ((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ) * e
          secondMixed :=
            -4 * (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) * d +
              (((Real.cos angle : ℝ) : ℂ) ^ 2 - ((Real.sin angle : ℝ) : ℂ) ^ 2) * e }
      simpa [coefficients, AngularHarmonicCoefficients.eval, smul_eq_mul] using
        coefficients.integral_polarFourierRadialPhase z p

/-- Phase-weighted full-angle reduction of canonical harmonic coefficients at an arbitrary
real-space polar angle. -/
theorem AngularHarmonicCoefficients.integral_polarFourierRadialPhase_shifted
    (coefficients : AngularHarmonicCoefficients ℂ) (z p angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z (θ - angle)) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z *
            (((Real.cos angle : ℝ) : ℂ) * coefficients.firstCosine +
              ((Real.sin angle : ℝ) : ℂ) * coefficients.firstSine) +
          polarFourierSecondCosineAngularKernel z *
            (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                (((Real.sin angle : ℝ) : ℂ) ^ 2)) * coefficients.secondCosine +
              (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                coefficients.secondMixed)) := by
  simpa [AngularHarmonicCoefficients.eval, smul_eq_mul] using
    (integral_polarFourierRadialPhase_shifted_second_harmonics
      z p angle coefficients.constant coefficients.firstCosine coefficients.firstSine
      coefficients.secondCosine coefficients.secondMixed)

/-- Finite-cutoff polar Fourier transform of a complex scalar momentum field with the physical
momentum measure `d²p / (2πℏ)²` included exactly once. -/
noncomputable def finiteCutoffPhysicalMomentumPolarFourier
    (hbar pMax : ℝ) (field : ℝ → ℝ → ℂ) (r : Fin 2 → ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * physicalMomentumPolarFourierPhase hbar p θ r) * field p θ

/-- Finite-cutoff polar Fourier reduction of canonical harmonic coefficients at an arbitrary polar
real-space point. -/
theorem finiteCutoffPhysicalMomentumPolarFourier_polarPoint2D_harmonics
    (hbar pMax radius angle : ℝ) (coefficients : ℝ → AngularHarmonicCoefficients ℂ) :
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
        (fun p θ => (coefficients p).eval θ) (polarPoint2D radius angle) =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        ∫ p in (0 : ℝ)..pMax,
          (p : ℂ) *
            (polarFourierZerothAngularKernel (p * radius / hbar) * (coefficients p).constant +
              polarFourierFirstCosineAngularKernel (p * radius / hbar) *
                (((Real.cos angle : ℝ) : ℂ) * (coefficients p).firstCosine +
                  ((Real.sin angle : ℝ) : ℂ) * (coefficients p).firstSine) +
              polarFourierSecondCosineAngularKernel (p * radius / hbar) *
                (((((Real.cos angle : ℝ) : ℂ) ^ 2) -
                    (((Real.sin angle : ℝ) : ℂ) ^ 2)) * (coefficients p).secondCosine +
                  (((Real.cos angle : ℝ) : ℂ) * ((Real.sin angle : ℝ) : ℂ)) *
                    (coefficients p).secondMixed)) := by
  unfold finiteCutoffPhysicalMomentumPolarFourier
  apply congrArg (((momentumMeasurePrefactor hbar : ℝ) : ℂ) * ·)
  apply intervalIntegral.integral_congr
  intro p _
  simp_rw [physicalMomentumPolarFourierPhase_polarPoint2D]
  exact (coefficients p).integral_polarFourierRadialPhase_shifted
    (p * radius / hbar) p angle

end

end Transport
end QuantumTheory
