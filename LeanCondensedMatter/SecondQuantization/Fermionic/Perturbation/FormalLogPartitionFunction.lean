import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Compatibility API for normalized partition-series logarithms

The statistics-independent normalization now lives in
`Analysis/PowerSeries/Normalization.lean`, and Mathlib's `PowerSeries.logOf` is the authoritative
formal logarithm.  This module retains the existing second-quantization names as thin compatibility
abbreviations so downstream fermionic Dyson and diagrammatic APIs remain unchanged.

All constructions are coefficientwise formal power series.  No convergence or analytic partition-
function identification is claimed here.
-/

namespace SecondQuantization

open PowerSeries

/-- Compatibility name for the generic normalization by a series' constant coefficient. -/
noncomputable abbrev normalizePartitionSeries (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.normalizeByConstantCoeff Z

/-- Compatibility theorem for the generic normalization result. -/
theorem constantCoeff_normalizePartitionSeries {Z : PowerSeries ℂ} (hZ : constantCoeff Z ≠ 0) :
    constantCoeff (normalizePartitionSeries Z) = 1 :=
  PowerSeries.constantCoeff_normalizeByConstantCoeff hZ

/-- Compatibility name for Mathlib's authoritative formal logarithm `PowerSeries.logOf`. -/
noncomputable abbrev formalLogPartitionFunction (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.logOf Z

/-- The formal logarithm of a normalized series has vanishing constant coefficient. -/
theorem constantCoeff_formalLogPartitionFunction {Z : PowerSeries ℂ}
    (hZ : constantCoeff Z = 1) : constantCoeff (formalLogPartitionFunction Z) = 0 :=
  PowerSeries.constantCoeff_logOf hZ

/-- The order-`1` coefficient of `log Z` equals the order-`1` coefficient of `Z` itself. -/
@[simp]
theorem coeff_one_formalLogPartitionFunction {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) :
    PowerSeries.coeff 1 (formalLogPartitionFunction Z) = PowerSeries.coeff 1 Z := by
  have hsub : HasSubst (Z - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hZ1 : constantCoeff (Z - 1) = 0 := by simp [hZ]
  have hant : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
  have hpow : ∀ d, 2 ≤ d → PowerSeries.coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have he : 1 ≤ e := by omega
    rw [pow_succ', coeff_mul, hant]
    have hcoeff0 : PowerSeries.coeff 0 ((Z - 1) ^ e) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hZ1, zero_pow (by omega : e ≠ 0)]
    have hcoeff0' : PowerSeries.coeff 0 (Z - 1) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact hZ1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, hcoeff0', hcoeff0]
    ring
  have hterm : ∀ d : ℕ, d ≠ 1 →
      PowerSeries.coeff d (log ℂ) • PowerSeries.coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · simp
    · simp [hpow d (by omega)]
  rw [formalLogPartitionFunction, PowerSeries.logOf_eq, coeff_subst' hsub,
    finsum_eq_single _ 1 hterm, coeff_one_log, one_smul, pow_one, map_sub,
    PowerSeries.coeff_one]
  simp

end SecondQuantization
