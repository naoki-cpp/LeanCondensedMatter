import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Normalization of power series by their constant coefficient

For a power series with nonzero constant coefficient, multiplication by its inverse produces a
series with constant coefficient `1`. Mathlib's `PowerSeries.logOf` is the authoritative formal
logarithm.
-/

namespace PowerSeries

variable {R : Type*} [Field R]

/-- Normalize a power series by multiplying it by the inverse of its constant coefficient. -/
noncomputable def normalizeByConstantCoeff (Z : PowerSeries R) : PowerSeries R :=
  C (constantCoeff Z)⁻¹ * Z

/-- Coefficients of a normalized series are scaled by the inverse constant coefficient. -/
@[simp]
theorem coeff_normalizeByConstantCoeff (Z : PowerSeries R) (n : ℕ) :
    coeff n (normalizeByConstantCoeff Z) = (constantCoeff Z)⁻¹ * coeff n Z := by
  simp [normalizeByConstantCoeff]

/-- A power series normalized by a nonzero constant coefficient has constant coefficient `1`. -/
theorem constantCoeff_normalizeByConstantCoeff {Z : PowerSeries R}
    (hZ : constantCoeff Z ≠ 0) :
    constantCoeff (normalizeByConstantCoeff Z) = 1 := by
  rw [normalizeByConstantCoeff, map_mul, constantCoeff_C, inv_mul_cancel₀ hZ]

/-- The order-one coefficient of `logOf Z` equals the order-one coefficient of a normalized
complex power series `Z`. -/
@[simp]
theorem coeff_one_logOf {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) :
    coeff 1 (logOf Z) = coeff 1 Z := by
  have hsub : HasSubst (Z - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hZ1 : constantCoeff (Z - 1) = 0 := by simp [hZ]
  have hant : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
  have hpow : ∀ d, 2 ≤ d → coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : 1 ≤ e := by omega
    rw [pow_succ', coeff_mul, hant]
    have hcoeff0 : coeff 0 ((Z - 1) ^ e) = 0 := by
      rw [coeff_zero_eq_constantCoeff, map_pow, hZ1, zero_pow (by omega : e ≠ 0)]
    have hcoeff0' : coeff 0 (Z - 1) = 0 := by
      rw [coeff_zero_eq_constantCoeff]
      exact hZ1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, hcoeff0', hcoeff0]
    ring
  have hterm : ∀ d : ℕ, d ≠ 1 →
      coeff d (log ℂ) • coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · simp
    · simp [hpow d (by omega)]
  rw [logOf_eq, coeff_subst' hsub, finsum_eq_single _ 1 hterm, coeff_one_log,
    one_smul, pow_one, map_sub, coeff_one]
  simp

end PowerSeries
