import LeanCondensedMatter.Analysis.SpecialFunctions.Bessel.HypergeometricSeries
import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Analytic derivative of the zeroth Bessel J function

The regularized hypergeometric coefficient shift proves the derivative
identity `J₀'(z) = -J₁(z)` at every complex argument, including the origin.
This argument is independent of Fourier kernels and transport models.
-/

namespace BesselHypergeometric

noncomputable section

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
theorem besselJ_zero_hasDerivAt (w : ℂ) :
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

end
end BesselHypergeometric
