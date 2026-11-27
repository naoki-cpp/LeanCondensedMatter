import Mathlib.Analysis.SpecialFunctions.Bessel
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Hypergeometric series and identities for complex Bessel J functions

The regularized hypergeometric coefficients give the J₀ series, the
three-term recurrence and derivative for arbitrary natural-number orders.
These identities hold at all complex arguments, including the origin.
The Fourier-angular applications are separate consumers.
-/

namespace BesselHypergeometric

/-- The coefficient of the regularized hypergeometric series with lower parameter `k + 1`. -/
theorem regularizedHGFunCoeff_zero_singleton_nat_add_one (k n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} n =
      1 / ((Nat.factorial n : ℂ) * (Nat.factorial (n + k) : ℂ)) := by
  have hgamma : Complex.Gamma (((k : ℂ) + 1) + (n : ℂ)) =
      (Nat.factorial (n + k) : ℂ) := by
    rw [show ((k : ℂ) + 1) + (n : ℂ) = ((n + k : ℕ) : ℂ) + 1 by
      simp only [Nat.cast_add]
      ring]
    exact Complex.Gamma_nat_eq_factorial (n + k)
  simp [Complex.regularizedHGFunCoeff, Nat.cast_add, hgamma]

/-- Differentiating a regularized hypergeometric coefficient shifts its lower parameter. -/
theorem regularizedHGFunCoeff_index_shift (k n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} (n + 1) =
      Complex.regularizedHGFunCoeff 0 {((k + 2 : ℕ) : ℂ)} n := by
  rw [regularizedHGFunCoeff_zero_singleton_nat_add_one k (n + 1),
    regularizedHGFunCoeff_zero_singleton_nat_add_one (k + 1) n,
    show n + 1 + k = n + (k + 1) by ac_rfl, Nat.factorial_succ n]
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hg : ((n + (k + 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [hn, hf, hg]

/-- Shifting the lower parameter multiplies the coefficient by the corresponding factorial step. -/
private theorem regularizedHGFunCoeff_parameter_shift (k n : ℕ) :
    ((n + k + 1 : ℕ) : ℂ) * Complex.regularizedHGFunCoeff 0 {((k + 2 : ℕ) : ℂ)} n =
      Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} n := by
  rw [regularizedHGFunCoeff_zero_singleton_nat_add_one (k + 1) n,
    regularizedHGFunCoeff_zero_singleton_nat_add_one k n]
  change ((n + k + 1 : ℕ) : ℂ) *
    (1 / ((n.factorial : ℂ) * ((n + k + 1).factorial : ℂ))) = _
  rw [Nat.factorial_succ (n + k)]
  push_cast
  have hn : (n : ℂ) + (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + k)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hg : ((n + k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- The regularized hypergeometric function with empty upper parameters is its scalar series. -/
theorem regularizedHGFun_zero_eq_tsum (b : Multiset ℂ) (w : ℂ) :
    Complex.regularizedHGFun 0 b w =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 b n * w ^ n := by
  rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
    ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- The scalar series with empty upper parameters is summable at every complex argument. -/
theorem summable_regularizedHGFun_zero (b : Multiset ℂ) (w : ℂ) :
    Summable (fun n : ℕ => Complex.regularizedHGFunCoeff 0 b n * w ^ n) := by
  simpa only [Complex.regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using
    (Complex.regularizedHGFunSeries 0 b).summable (by simp)

/-- Mathlib's integer-order Bessel function has the expected coefficient expansion. -/
theorem besselJZero_eq_regularizedHGTsum (z : ℂ) :
    Complex.besselJ 0 z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {(1 : ℂ)} n *
        (-(z / 2) ^ 2) ^ n := by
  rw [Complex.besselJ_def]
  simp only [Complex.cpow_zero, one_mul, zero_add]
  exact regularizedHGFun_zero_eq_tsum {(1 : ℂ)} (-(z / 2) ^ 2)

/-! ## Three-term recurrence -/

noncomputable section

/-- At a natural-number order the complex Bessel function uses an ordinary
natural power, so its representation is valid also at the origin. -/
theorem besselJ_nat_eq (k : ℕ) (z : ℂ) :
    Complex.besselJ (k : ℂ) z =
      (z / 2) ^ k * Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)} (-(z / 2) ^ 2) := by
  simp only [Complex.besselJ_def, Complex.cpow_natCast, Nat.cast_add, Nat.cast_one]

/-- Adjacent positive integer lower parameters satisfy the contiguous relation
behind the natural-order Bessel recurrence. -/
private theorem regularizedHGFun_zero_singleton_nat_recurrence (k : ℕ) (w : ℂ) :
    Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)} w -
      ((k + 1 : ℕ) : ℂ) * Complex.regularizedHGFun 0 {((k + 2 : ℕ) : ℂ)} w =
        w * Complex.regularizedHGFun 0 {((k + 3 : ℕ) : ℂ)} w := by
  let c1 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)}
  let c2 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {((k + 2 : ℕ) : ℂ)}
  let c3 : ℕ → ℂ := Complex.regularizedHGFunCoeff 0 {((k + 3 : ℕ) : ℂ)}
  have hcoeff (n : ℕ) :
      c1 (n + 1) - ((k + 1 : ℕ) : ℂ) * c2 (n + 1) = c3 n := by
    have h12 : ((n + 1 + k + 1 : ℕ) : ℂ) * c2 (n + 1) = c1 (n + 1) :=
      regularizedHGFunCoeff_parameter_shift k (n + 1)
    have h23 : ((n + 1 : ℕ) : ℂ) * c2 (n + 1) = c3 n :=
      regularizedHGFunCoeff_index_shift (k + 1) n
    simp only [Nat.cast_add, Nat.cast_one] at h12 h23 ⊢
    linear_combination -h12 + h23
  have hzero : c1 0 - ((k + 1 : ℕ) : ℂ) * c2 0 = 0 := by
    apply sub_eq_zero.mpr
    simpa only [c1, c2, Nat.zero_add] using
      (regularizedHGFunCoeff_parameter_shift k 0).symm
  have hs1 : Summable (fun n : ℕ => c1 n * w ^ n) :=
    summable_regularizedHGFun_zero {((k + 1 : ℕ) : ℂ)} w
  have hs2 : Summable (fun n : ℕ => c2 n * w ^ n) :=
    summable_regularizedHGFun_zero {((k + 2 : ℕ) : ℂ)} w
  rw [regularizedHGFun_zero_eq_tsum {((k + 1 : ℕ) : ℂ)},
    regularizedHGFun_zero_eq_tsum {((k + 2 : ℕ) : ℂ)},
    regularizedHGFun_zero_eq_tsum {((k + 3 : ℕ) : ℂ)}]
  change (∑' n : ℕ, c1 n * w ^ n) -
      ((k + 1 : ℕ) : ℂ) * (∑' n : ℕ, c2 n * w ^ n) =
        w * ∑' n : ℕ, c3 n * w ^ n
  have hs2' := hs2.mul_left ((k + 1 : ℕ) : ℂ)
  calc
    _ = ∑' n : ℕ, (c1 n * w ^ n - ((k + 1 : ℕ) : ℂ) * (c2 n * w ^ n)) := by
      rw [hs1.tsum_sub hs2', tsum_mul_left]
    _ = ∑' n : ℕ, w * (c3 n * w ^ n) := by
      rw [(hs1.sub hs2').tsum_eq_zero_add]
      simp only [pow_zero, mul_one, hzero, zero_add]
      apply tsum_congr
      intro n
      calc
        _ = (c1 (n + 1) - ((k + 1 : ℕ) : ℂ) * c2 (n + 1)) * w ^ (n + 1) := by ring
        _ = _ := by rw [hcoeff, pow_succ]; ring
    _ = _ := by rw [tsum_mul_left]

/-- Three-term recurrence for every nonnegative integer Bessel order.
No division by the argument is needed, so the identity holds at zero. -/
theorem besselJ_nat_recurrence (k : ℕ) (z : ℂ) :
    2 * ((k + 1 : ℕ) : ℂ) * Complex.besselJ ((k + 1 : ℕ) : ℂ) z =
      z * (Complex.besselJ (k : ℂ) z + Complex.besselJ ((k + 2 : ℕ) : ℂ) z) := by
  rw [besselJ_nat_eq (k + 1), besselJ_nat_eq k, besselJ_nat_eq (k + 2)]
  have h := regularizedHGFun_zero_singleton_nat_recurrence k (-(z / 2) ^ 2)
  simp only [pow_succ] at h ⊢
  linear_combination -z * (z / 2) ^ k * h

/-- The Bessel recurrence eliminates the apparent singularity of J₁(z)²/z
at the origin, with the convention that division by zero is zero. -/
theorem besselJ_one_sq_div_eq_half_product (z : ℝ) :
    Complex.besselJ 1 (z : ℂ) ^ 2 / (z : ℂ) =
      Complex.besselJ 1 (z : ℂ) *
        (Complex.besselJ 0 (z : ℂ) + Complex.besselJ 2 (z : ℂ)) / 2 := by
  by_cases hz : z = 0
  · subst z
    simp [Complex.besselJ_zero]
  · have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
    apply (div_eq_iff hzc).2
    have hrec : 2 * Complex.besselJ 1 (z : ℂ) =
        (z : ℂ) * (Complex.besselJ 0 (z : ℂ) + Complex.besselJ 2 (z : ℂ)) := by
      simpa using besselJ_nat_recurrence 0 (z : ℂ)
    linear_combination (Complex.besselJ 1 (z : ℂ) / 2) * hrec

/-! ## Analytic derivatives at natural-number orders -/

/-- Differentiating the regularized hypergeometric function with positive integer
lower parameter shifts that parameter by one. -/
theorem regularizedHGFun_zero_singleton_nat_hasDerivAt (k : ℕ) (w : ℂ) :
    HasDerivAt (Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)})
      (Complex.regularizedHGFun 0 {((k + 2 : ℕ) : ℂ)} w) w := by
  let p := Complex.regularizedHGFunSeries 0 {((k + 1 : ℕ) : ℂ)}
  have hradius : ‖w‖ₑ < p.radius := by
    simp [p]
  have hderivRadius : p.derivSeries.radius = ⊤ := by
    apply top_unique
    simpa [p] using p.radius_le_radius_derivSeries
  have hsummable : Summable (fun n : ℕ => p.derivSeries n (fun _ => w)) :=
    p.derivSeries.summable (by simp [hderivRadius])
  have hsum :
      (p.derivSeries.sum w) (1 : ℂ) =
        Complex.regularizedHGFun 0 {((k + 2 : ℕ) : ℂ)} w := by
    calc
      (p.derivSeries.sum w) (1 : ℂ) =
          ∑' n : ℕ, (p.derivSeries n (fun _ => w)) (1 : ℂ) := by
        exact tsum_apply hsummable 1
      _ = ∑' n : ℕ,
          (((n + 1 : ℕ) : ℂ) *
            Complex.regularizedHGFunCoeff 0 {((k + 1 : ℕ) : ℂ)} (n + 1)) * w ^ n := by
        apply tsum_congr
        intro n
        simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
          smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
          smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        simp only [p, Complex.regularizedHGFunSeries_coeff, Nat.cast_add, Nat.cast_one]
        ring_nf
      _ = ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {((k + 2 : ℕ) : ℂ)} n * w ^ n := by
        apply tsum_congr
        intro n
        rw [regularizedHGFunCoeff_index_shift]
      _ = Complex.regularizedHGFun 0 {((k + 2 : ℕ) : ℂ)} w :=
        (regularizedHGFun_zero_eq_tsum {((k + 2 : ℕ) : ℂ)} w).symm
  have hderiv : HasDerivAt (Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)})
      ((p.derivSeries.sum w) 1) w := by
    change HasDerivAt p.sum ((p.derivSeries.sum w) 1) w
    exact (p.hasFDerivAt_sum hradius).hasDerivAt
  rw [hsum] at hderiv
  exact hderiv

/-- Derivative of the complex Bessel function at every nonnegative integer order.
The expression avoids division by the argument and is valid at zero. -/
theorem besselJ_nat_hasDerivAt (k : ℕ) (w : ℂ) :
    HasDerivAt (Complex.besselJ (k : ℂ))
      (((k : ℂ) * (w / 2) ^ (k - 1) * (1 / 2 : ℂ)) *
        Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)} (-(w / 2) ^ 2) -
          Complex.besselJ ((k + 1 : ℕ) : ℂ) w) w := by
  have harg : HasDerivAt (fun t : ℂ => -(t / 2) ^ 2) (-(w / 2)) w := by
    convert (((hasDerivAt_id w).div_const (2 : ℂ)).pow 2).neg using 1
    · funext t
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring_nf
  have hp : HasDerivAt (fun t : ℂ => (t / 2) ^ k)
      ((k : ℂ) * (w / 2) ^ (k - 1) * (1 / 2 : ℂ)) w :=
    ((hasDerivAt_id w).div_const (2 : ℂ)).pow k
  have hh : HasDerivAt
      (fun t : ℂ => Complex.regularizedHGFun 0 {((k + 1 : ℕ) : ℂ)} (-(t / 2) ^ 2))
      (Complex.regularizedHGFun 0 {((k + 2 : ℕ) : ℂ)} (-(w / 2) ^ 2) * (-(w / 2))) w :=
    (regularizedHGFun_zero_singleton_nat_hasDerivAt k (-(w / 2) ^ 2)).comp w harg
  convert hp.mul hh using 1
  · funext t
    exact besselJ_nat_eq k t
  · rw [besselJ_nat_eq (k + 1) w, pow_succ]
    ring


end
end BesselHypergeometric
