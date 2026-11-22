import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.ThreeTermRecurrence
import LeanCondensedMatter.Analysis.Fourier.AngularHarmonics
import LeanCondensedMatter.Analysis.Fourier.FullAngleCosineMoments
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Model-independent polar Fourier–Bessel kernels

This module develops the dimensionless polar Fourier phase, angular harmonics,
Bessel-function representations, symmetry identities, differentiation formulas,
and full-period harmonic reduction. It assumes no momentum measure, Planck
constant, physical Fourier normalization, transport mechanism, or Hamiltonian.

The existing declaration namespace is preserved during the first file-ownership
migration to avoid a breaking repository-wide declaration rename. The mathematical
module itself depends only on Analysis and Mathlib.
-/

namespace QuantumTheory

open AngularHarmonics
namespace Transport

open BesselHypergeometric

noncomputable section

open MeasureTheory
open scoped Interval ComplexConjugate

/-- Dimensionless radial phase `exp(i z cos θ)` that appears after aligning the real-space point with
the polar axis. -/
def polarFourierRadialPhase (z θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ)))

/-- Zeroth full-angle radial Fourier kernel, identified with `2π J₀(z)` by
`polarFourierZerothAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierZerothAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), polarFourierRadialPhase z θ

/-- First cosine full-angle radial Fourier kernel, identified with `2π i J₁(z)`
by `polarFourierFirstCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierFirstCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ * ((Real.cos θ : ℝ) : ℂ)

/-- The zeroth full-angle Fourier phase has vanishing first cosine harmonic. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_zero :
    polarFourierFirstCosineAngularKernel 0 = 0 := by
  have h := integral_cos_mul_complex (z := (1 : ℂ)) one_ne_zero (0 : ℝ) (2 * Real.pi)
  simpa [polarFourierFirstCosineAngularKernel, polarFourierRadialPhase] using h
/-- Second cosine full-angle radial Fourier kernel, written as the `cos(2θ)`
polynomial for quadratic angular products and identified with `-2π J₂(z)`
by `polarFourierSecondCosineAngularKernel_eq_besselJ`. -/
noncomputable def polarFourierSecondCosineAngularKernel (z : ℝ) : ℂ :=
  ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
    polarFourierRadialPhase z θ *
      ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

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
  have hfact : (0 : ℝ) ≤ (Nat.factorial n : ℝ) := by positivity
  have hpow : (0 : ℝ) ≤ |z| ^ n := pow_nonneg (abs_nonneg z) _
  have hmoment := fullAngleCosineMoment_norm_le n
  calc
    ‖(Complex.I * (z : ℂ)) ^ n / (Nat.factorial n : ℂ) *
        (fullAngleCosineMoment n : ℂ)‖ =
        (|z| ^ n / (Nat.factorial n : ℝ)) *
          ‖fullAngleCosineMoment n‖ := by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_I,
        Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
        one_mul]
    _ ≤ (|z| ^ n / (Nat.factorial n : ℝ)) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hmoment (div_nonneg hpow hfact)
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

/-- Differentiate a polar Fourier angular integral with any continuous weight bounded by one.
The common domination estimate also covers higher bounded angular harmonics. -/
private theorem polarFourierWeightedAngularKernel_hasDerivAt
    (weight : ℝ → ℂ) (hweight : Continuous weight)
    (hbound : ∀ θ : ℝ, ‖weight θ‖ ≤ 1) (z : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        polarFourierRadialPhase x θ * weight θ)
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * weight θ) z := by
  let derivative : ℝ → ℝ → ℂ := fun x θ =>
    (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
      polarFourierRadialPhase x θ) * weight θ
  have hdiff (x θ : ℝ) :
      HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ * weight θ)
        (derivative x θ) x := by
    have hmul : HasDerivAt (fun t : ℝ => t * Real.cos θ)
        (Real.cos θ) x := by
      simpa using (hasDerivAt_id x).mul_const (Real.cos θ)
    have harg : HasDerivAt
        (fun t : ℝ => Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
        (Complex.I * ((Real.cos θ : ℝ) : ℂ)) x :=
      hmul.ofReal_comp |>.const_mul Complex.I
    have hphase := (Complex.hasDerivAt_exp _).comp x harg
    have hbase : HasDerivAt (fun t : ℝ => polarFourierRadialPhase t θ)
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase x θ) x := by
      convert hphase using 1
      · rfl
      · dsimp [polarFourierRadialPhase]
        ring
    exact hbase.mul_const (weight θ)
  have hcont (x : ℝ) : Continuous (fun θ : ℝ =>
      polarFourierRadialPhase x θ * weight θ) := by
    apply Continuous.mul
    · change Continuous (fun θ : ℝ =>
        Complex.exp (Complex.I * (((x * Real.cos θ : ℝ) : ℂ))))
      fun_prop
    · exact hweight
  have hcont' (x : ℝ) : Continuous (derivative x) := by
    dsimp only [derivative]
    apply Continuous.mul
    · change Continuous (fun θ : ℝ =>
        Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          Complex.exp (Complex.I * (((x * Real.cos θ : ℝ) : ℂ))))
      fun_prop
    · exact hweight
  have hderivBound (x θ : ℝ) : ‖derivative x θ‖ ≤ (1 : ℝ) := by
    have hnorm : ‖derivative x θ‖ = |Real.cos θ| * ‖weight θ‖ := by
      simp only [derivative, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, norm_polarFourierRadialPhase, one_mul, mul_one]
    rw [hnorm]
    calc
      |Real.cos θ| * ‖weight θ‖ ≤ 1 * ‖weight θ‖ :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _)
      _ = ‖weight θ‖ := one_mul _
      _ ≤ 1 := hbound θ
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => polarFourierRadialPhase x θ * weight θ)
    (F' := derivative)
    (bound := fun _θ : ℝ => (1 : ℝ))
    (s := Set.univ) (x₀ := z) (a := (0 : ℝ)) (b := 2 * Real.pi)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont z).intervalIntegrable _ _)
    ((hcont' z).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun θ _ x _ => hderivBound x θ)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun θ _ x _ => hdiff x θ)).2

/-- The first nonzero-argument differential relation of the radial Fourier
harmonics: the derivative of the zeroth angular kernel is `i` times the
first-cosine kernel.

Unlike an origin-only normalization, this holds for every real Fourier
argument. Together with the J₀ Bessel bridge and the hypergeometric-series
derivative, it yields the first-harmonic Bessel identity. -/
theorem polarFourierZerothAngularKernel_hasDerivAt (z : ℝ) :
    HasDerivAt polarFourierZerothAngularKernel
      (Complex.I * polarFourierFirstCosineAngularKernel z) z := by
  have h := polarFourierWeightedAngularKernel_hasDerivAt
    (fun _ : ℝ => (1 : ℂ)) continuous_const (by intro θ; simp) z
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * (1 : ℂ)) =
        Complex.I * polarFourierFirstCosineAngularKernel z := by
    unfold polarFourierFirstCosineAngularKernel
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [hrew] at h
  change HasDerivAt
    (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase x θ)
    (Complex.I * polarFourierFirstCosineAngularKernel z) z
  simpa only [mul_one] using h

/-- The derivative of the regularized hypergeometric series with bottom parameter 1
has bottom parameter 2. This is the coefficient identity behind `J₀' = -J₁`. -/
private theorem regularizedHGFun_zero_one_hasDerivAt (w : ℂ) :
    HasDerivAt (Complex.regularizedHGFun 0 {(1 : ℂ)})
      (Complex.regularizedHGFun 0 {(2 : ℂ)} w) w := by
  let p := Complex.regularizedHGFunSeries 0 {(1 : ℂ)}
  have hcoeff (n : ℕ) :
      ((n + 1 : ℕ) : ℂ) * Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} (n + 1) =
        Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n := by
    have h0 := regularizedHGFunCoeff_zero_singleton_nat_add_one 0 (n + 1)
    have h1 := regularizedHGFunCoeff_zero_singleton_nat_add_one 1 n
    norm_num only [Nat.add_zero] at h0 h1
    rw [h0, h1, ← pow_two, Nat.factorial_succ]
    push_cast
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (Nat.factorial n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have hradius : ‖w‖ₑ < p.radius := by
    simp [p]
  have hderivRadius : p.derivSeries.radius = ⊤ := by
    apply top_unique
    simpa [p] using p.radius_le_radius_derivSeries
  have hsummable : Summable (fun n : ℕ => p.derivSeries n (fun _ => w)) :=
    p.derivSeries.summable (by simp [hderivRadius])
  have hsum :
      (p.derivSeries.sum w) (1 : ℂ) =
        Complex.regularizedHGFun 0 {(2 : ℂ)} w := by
    calc
      (p.derivSeries.sum w) (1 : ℂ) =
          ∑' n : ℕ, (p.derivSeries n (fun _ => w)) (1 : ℂ) := by
        exact tsum_apply hsummable 1
      _ = ∑' n : ℕ,
          (((n + 1 : ℕ) : ℂ) *
            Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} (n + 1)) * w ^ n := by
        apply tsum_congr
        intro n
        simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
          smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        simp only [p, Complex.regularizedHGFunSeries_coeff]
        ring_nf
      _ = ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {(2 : ℂ)} n * w ^ n := by
        apply tsum_congr
        intro n
        rw [hcoeff]
      _ = Complex.regularizedHGFun 0 {(2 : ℂ)} w := by
        rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
          ← FormalMultilinearSeries.ofScalarsSum,
          FormalMultilinearSeries.ofScalars_sum_eq]
        simp only [smul_eq_mul]
  have hderiv : HasDerivAt (Complex.regularizedHGFun 0 {(1 : ℂ)})
      ((p.derivSeries.sum w) 1) w := by
    change HasDerivAt p.sum ((p.derivSeries.sum w) 1) w
    exact (p.hasFDerivAt_sum hradius).hasDerivAt
  rw [hsum] at hderiv
  exact hderiv

/-- Derivative of the zeroth complex Bessel function obtained from its
regularized hypergeometric coefficients. -/
private theorem besselJ_zero_hasDerivAt (w : ℂ) :
    HasDerivAt (Complex.besselJ 0) (-Complex.besselJ 1 w) w := by
  have harg : HasDerivAt (fun t : ℂ => -(t / 2) ^ 2) (-(w / 2)) w := by
    convert (((hasDerivAt_id w).div_const (2 : ℂ)).pow 2).neg using 1
    · funext t
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring_nf
  have h := (regularizedHGFun_zero_one_hasDerivAt (-(w / 2) ^ 2)).comp w harg
  convert h using 1
  · funext t
    simp [Complex.besselJ_def]
  · simp [Complex.besselJ_def]
    ring

/-- The first angular Fourier harmonic is the correctly normalized Bessel function
`J₁`, for every real radial Fourier argument. -/
theorem polarFourierFirstCosineAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierFirstCosineAngularKernel z =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I * Complex.besselJ 1 (z : ℂ) := by
  have hfun :
      (fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
        Complex.besselJ 0 (t : ℂ)) = polarFourierZerothAngularKernel := by
    funext t
    exact (polarFourierZerothAngularKernel_eq_besselJ t).symm
  have hJ := ((besselJ_zero_hasDerivAt (z : ℂ)).comp_ofReal).const_mul
    ((2 * Real.pi : ℝ) : ℂ)
  change HasDerivAt
    (fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 0 (t : ℂ))
    (((2 * Real.pi : ℝ) : ℂ) * -Complex.besselJ 1 (z : ℂ)) z at hJ
  rw [hfun] at hJ
  have hderiv := (polarFourierZerothAngularKernel_hasDerivAt z).unique hJ
  have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      _ = -(Complex.I ^ 2) := by ring
      _ = 1 := by rw [Complex.I_sq]; ring
  calc
    polarFourierFirstCosineAngularKernel z =
        ((-Complex.I) * Complex.I) * polarFourierFirstCosineAngularKernel z := by
      rw [hI, one_mul]
    _ = (-Complex.I) * (Complex.I * polarFourierFirstCosineAngularKernel z) := by
      ring
    _ = ((2 * Real.pi : ℝ) : ℂ) * Complex.I * Complex.besselJ 1 (z : ℂ) := by
      rw [hderiv]
      ring

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
      ((-Complex.I * (z : ℂ) * sine θ) * phase θ) θ :=
    polarFourierRadialPhase_hasDerivAt z
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
      volume 0 (2 * Real.pi) :=
    (hccos.mul hcphase).intervalIntegrable _ _
  have hsinSqInt : IntervalIntegrable
      (fun θ : ℝ => phase θ * sine θ ^ 2) volume 0 (2 * Real.pi) :=
    (hcphase.mul (hcsin.pow 2)).intervalIntegrable _ _
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
    simpa [polarFourierFirstCosineAngularKernel, cosine, phase, mul_comm] using hfirst
  calc
    2 * polarFourierFirstCosineAngularKernel z =
        (Complex.I * (z : ℂ)) *
          (2 * (∫ θ in (0 : ℝ)..(2 * Real.pi), phase θ * sine θ ^ 2)) := by
      rw [hfirstKernel]
      ring
    _ = _ := by rw [hsecond]

/-- The second-cosine angular Fourier kernel vanishes at zero radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_zero :
    polarFourierSecondCosineAngularKernel 0 = 0 := by
  let coefficients : AngularHarmonicCoefficients ℂ :=
    { constant := 0
      firstCosine := 0
      firstSine := 0
      secondCosine := 1
      secondMixed := 0 }
  have h := coefficients.integral_eval
  simpa [coefficients, AngularHarmonicCoefficients.eval,
    polarFourierSecondCosineAngularKernel, polarFourierRadialPhase,
    smul_eq_mul] using h

/-- The second cosine angular Fourier kernel is the normalized Bessel function
`-2π J₂`, for every real radial argument. -/
theorem polarFourierSecondCosineAngularKernel_eq_besselJ (z : ℝ) :
    polarFourierSecondCosineAngularKernel z =
      -(((2 * Real.pi : ℝ) : ℂ) * Complex.besselJ 2 (z : ℂ)) := by
  by_cases hz : z = 0
  · subst z
    simp [Complex.besselJ_zero]
  · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
    have hK := polarFourierFirstCosineAngularKernel_two_mul_eq_zeroth_sub_second z
    rw [polarFourierFirstCosineAngularKernel_eq_besselJ,
      polarFourierZerothAngularKernel_eq_besselJ] at hK
    have hJ := besselJ_zero_one_two_recurrence (z : ℂ)
    apply mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hzc)
    linear_combination hK - (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * hJ

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

/-- Reflection across π makes the full-period integral of an antisymmetric
complex-valued integrand vanish. -/
private theorem integral_fullPeriod_eq_zero_of_reflection_neg
    (f : ℝ → ℂ) (hneg : ∀ θ, f (2 * Real.pi - θ) = -f θ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) = 0 := by
  have hsub :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi))
  have hflip :
      (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (2 * Real.pi - θ)) =
        -(∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ) := by
    simp_rw [hneg, intervalIntegral.integral_neg]
  exact CharZero.neg_eq_self_iff.mp (hflip.symm.trans hsub)

/-- The sine first harmonic vanishes against the radial Fourier phase over one full angle. -/
theorem integral_polarFourierRadialPhase_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ * ((Real.sin θ : ℝ) : ℂ)) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- The mixed quadratic harmonic `cos θ sin θ` vanishes against the radial Fourier phase over one
full angle. -/
theorem integral_polarFourierRadialPhase_mul_cos_mul_sin_zero (z : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase z θ *
        (((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ))) = 0 := by
  apply integral_fullPeriod_eq_zero_of_reflection_neg
  intro θ
  unfold polarFourierRadialPhase
  rw [Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  push_cast
  ring

/-- Phase-weighted full-angle integration of the canonical constant/first/second harmonic
decomposition. The first-sine and mixed-second channels vanish on the radial axis. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients
    (coefficients : AngularHarmonicCoefficients ℂ) (z p : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
      ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
      (p : ℂ) *
        (polarFourierZerothAngularKernel z * coefficients.constant +
          polarFourierFirstCosineAngularKernel z * coefficients.firstCosine +
          polarFourierSecondCosineAngularKernel z * coefficients.secondCosine) := by
  calc
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * polarFourierRadialPhase z θ) * coefficients.eval θ) =
        (p : ℂ) * ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi),
          polarFourierRadialPhase z θ * coefficients.eval θ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = _ := by
      congr 1
      simp only [AngularHarmonicCoefficients.eval, smul_eq_mul]
      simp_rw [mul_add, ← mul_assoc]
      repeat' rw [intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)
        (by apply Continuous.intervalIntegrable; unfold polarFourierRadialPhase; fun_prop)]
      simp only [intervalIntegral.integral_mul_const]
      simp_rw [mul_assoc]
      simp only [integral_polarFourierRadialPhase_mul_sin_zero,
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
    integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

/-- The zeroth full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierZerothAngularKernel_neg (z : ℝ) :
    polarFourierZerothAngularKernel (-z) =
      polarFourierZerothAngularKernel z := by
  simp only [polarFourierZerothAngularKernel_eq_besselJ, Complex.ofReal_neg]
  congr 1
  simpa only [Int.cast_zero] using
    (Complex.even_besselJ (a := (0 : ℤ)) (by norm_num)) (z : ℂ)

/-- The first-cosine full-angle radial Fourier kernel is odd in its radial argument. -/
@[simp] theorem polarFourierFirstCosineAngularKernel_neg (z : ℝ) :
    polarFourierFirstCosineAngularKernel (-z) =
      -polarFourierFirstCosineAngularKernel z := by
  have hodd : Complex.besselJ 1 (-(z : ℂ)) =
      -Complex.besselJ 1 (z : ℂ) := by
    simpa only [Int.cast_one] using
      (Complex.odd_besselJ (a := (1 : ℤ)) (by norm_num)) (z : ℂ)
  simp only [polarFourierFirstCosineAngularKernel_eq_besselJ, Complex.ofReal_neg,
    hodd]
  ring

/-- The second-cosine full-angle radial Fourier kernel is even in its radial argument. -/
@[simp] theorem polarFourierSecondCosineAngularKernel_neg (z : ℝ) :
    polarFourierSecondCosineAngularKernel (-z) =
      polarFourierSecondCosineAngularKernel z := by
  have heven : Complex.besselJ 2 (-(z : ℂ)) =
      Complex.besselJ 2 (z : ℂ) := by
    simpa using (Complex.even_besselJ (a := (2 : ℤ)) (by norm_num)) (z : ℂ)
  simp only [polarFourierSecondCosineAngularKernel_eq_besselJ, Complex.ofReal_neg,
    heven]

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
      simp_rw [polarFourierRadialPhase_conj]
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
      simp_rw [map_mul, Complex.conj_ofReal, polarFourierRadialPhase_conj]
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
      simp_rw [map_mul, map_sub, map_pow, Complex.conj_ofReal,
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

/-- Full-period integrals are unchanged by translating a periodic integrand.
This is also needed for Fourier harmonics at arbitrary polar angles. -/
private theorem intervalIntegral_fullPeriod_comp_sub_eq
    (f : ℝ → ℂ) (hf : Function.Periodic f (2 * Real.pi)) (angle : ℝ) :
    (∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f (θ - angle)) =
      ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), f θ := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h := hf.intervalIntegral_add_eq (-angle) 0
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

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
        integral_polarFourierRadialPhase_harmonicCoefficients coefficients z p

/-- Phase-weighted full-angle reduction of canonical harmonic coefficients at an arbitrary
real-space polar angle. -/
theorem integral_polarFourierRadialPhase_harmonicCoefficients_shifted
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

/-- Differentiating the first polar Fourier harmonic produces precisely the
isotropic plus second-harmonic channels. This is an all-real-argument
differential identity, not an origin-only or asymptotic statement. -/
theorem polarFourierFirstCosineAngularKernel_hasDerivAt (z : ℝ) :
    HasDerivAt polarFourierFirstCosineAngularKernel
      ((Complex.I / 2) *
        (polarFourierZerothAngularKernel z +
          polarFourierSecondCosineAngularKernel z)) z := by
  let derivative : ℝ → ℝ → ℂ := fun x θ =>
    Complex.I * ((((Real.cos θ : ℝ) : ℂ)) ^ 2) * polarFourierRadialPhase x θ
  have h := polarFourierWeightedAngularKernel_hasDerivAt
    (fun θ : ℝ => ((Real.cos θ : ℝ) : ℂ))
    (by fun_prop)
    (by
      intro θ
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ)
    z
  have hderiv :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.I * ((Real.cos θ : ℝ) : ℂ) *
          polarFourierRadialPhase z θ) * ((Real.cos θ : ℝ) : ℂ)) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) := by
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp [derivative]
    ring
  have hrew :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) =
        (Complex.I / 2) *
          (polarFourierZerothAngularKernel z +
            polarFourierSecondCosineAngularKernel z) := by
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi), derivative z θ) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (Complex.I / 2) *
              (polarFourierRadialPhase z θ +
                polarFourierRadialPhase z θ *
                  (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                    ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro θ _
        have hs : (((Real.sin θ : ℝ) : ℂ) ^ 2) +
            (((Real.cos θ : ℝ) : ℂ) ^ 2) = 1 := by
          exact_mod_cast Real.sin_sq_add_cos_sq θ
        dsimp [derivative]
        linear_combination (Complex.I / 2 * polarFourierRadialPhase z θ) * hs
      _ = (Complex.I / 2) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            polarFourierRadialPhase z θ +
              polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by
        rw [intervalIntegral.integral_add]
        · rfl
        · have hc : Continuous (polarFourierRadialPhase z) := by
            change Continuous (fun θ : ℝ =>
              Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))))
            fun_prop
          exact hc.intervalIntegrable _ _
        · have hc : Continuous (fun θ : ℝ =>
              polarFourierRadialPhase z θ *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2)) := by
            change Continuous (fun θ : ℝ =>
              Complex.exp (Complex.I * (((z * Real.cos θ : ℝ) : ℂ))) *
                (((Real.cos θ : ℝ) : ℂ) ^ 2 -
                  ((Real.sin θ : ℝ) : ℂ) ^ 2))
            fun_prop
          exact hc.intervalIntegrable _ _
  rw [hderiv, hrew] at h
  change HasDerivAt
    (fun x : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
      polarFourierRadialPhase x θ * ((Real.cos θ : ℝ) : ℂ))
    ((Complex.I / 2) *
      (polarFourierZerothAngularKernel z +
        polarFourierSecondCosineAngularKernel z)) z
  exact h

/-- A finite-radius conservation-law primitive for the first two radial Fourier
harmonics. Its derivative involves the same K0-minus-K2 channel that occurs in
the Gaussian-crossed current moments; the identity is valid including z = 0. -/
theorem polarFourierHarmonicEnergy_hasDerivAt (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        polarFourierZerothAngularKernel t ^ 2 -
          polarFourierFirstCosineAngularKernel t ^ 2)
      (Complex.I * polarFourierFirstCosineAngularKernel z *
        (polarFourierZerothAngularKernel z -
          polarFourierSecondCosineAngularKernel z)) z := by
  have h0 := (polarFourierZerothAngularKernel_hasDerivAt z).pow 2
  have h1 := (polarFourierFirstCosineAngularKernel_hasDerivAt z).pow 2
  convert h0.sub h1 using 1
  ring



end

end Transport
end QuantumTheory
