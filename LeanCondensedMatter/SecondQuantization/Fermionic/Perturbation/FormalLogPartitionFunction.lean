import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# The formal logarithm of a partition function

This file provides the low-level formal-power-series layer used by the completed finite-mode
fermionic Linked Cluster Theorem. It defines normalization by the zeroth-order partition coefficient
and the purely formal logarithm of the resulting series.

`log Z` is represented as a formal power series in a perturbation-strength parameter `λ`, for an
arbitrary `Z : PowerSeries ℂ` normalized to `Z(0) = 1`. A physical perturbative partition series
usually has constant term `Z₀ ≠ 1`, so `normalizePartitionSeries` first rescales by `Z₀⁻¹`.
`formalLogPartitionFunction` then substitutes `Z - 1` into Mathlib's universal series
`log(1+X) = X - X²/2 + X³/3 - ⋯`. This construction is coefficientwise and needs no convergence
hypothesis.

The general coefficient bridge now lives in `Combinatorics/PowerSeriesCumulant.lean`: factorial-
normalized coefficients of `PowerSeries.logOf Z` are finite-set cumulants of the factorial-normalized
coefficients of `Z`. The fermionic Dyson specialization and connected-diagram theorem are assembled in
`Fermionic/Diagrammatics/DysonLinkedClusterTheorem.lean`.

This file still makes no analytic claim that a formal Dyson series converges or equals an interacting
partition function. That is a separate later milestone; see
`notes/roadmaps/linked-cluster-theorem.md` and `notes/roadmaps/second-quantization.md`.
-/

namespace SecondQuantization

open PowerSeries

/-- **Normalize a partition-function series by its own zeroth-order value.** A genuine
perturbative partition function `Z(λ) = Z₀ + Z₁λ + ⋯` has `Z(0) = Z₀`, the free (unperturbed)
partition function, not `1`. `normalizePartitionSeries Z := Z₀⁻¹ • Z` rescales it to have constant
term `1`, so `formalLogPartitionFunction` below can be applied to it. -/
noncomputable def normalizePartitionSeries (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C (constantCoeff Z)⁻¹ * Z

theorem constantCoeff_normalizePartitionSeries {Z : PowerSeries ℂ} (hZ : constantCoeff Z ≠ 0) :
    constantCoeff (normalizePartitionSeries Z) = 1 := by
  rw [normalizePartitionSeries, map_mul, PowerSeries.constantCoeff_C, inv_mul_cancel₀ hZ]

/-- **The formal logarithm of a normalized partition-function series.** For `Z : PowerSeries ℂ`
with constant term `1` (i.e. `Z` already normalized by its zeroth-order value `Z(0)`), `log Z` is
the power series `log(1 + (Z - 1))`, obtained by substituting `Z - 1` into Mathlib's universal
`log(1+X)` series (`PowerSeries.log`). Well-defined purely formally: no convergence or topology is
needed, since `PowerSeries.subst` only ever inspects finitely many coefficients of `Z - 1` to
compute each coefficient of the result. -/
noncomputable def formalLogPartitionFunction (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.log ℂ).subst (Z - 1)

theorem hasSubst_sub_one_of_constantCoeff_eq_one {Z : PowerSeries ℂ}
    (hZ : constantCoeff Z = 1) : HasSubst (Z - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hZ])

/-- **`formalLogPartitionFunction` has vanishing constant term**, matching the physical picture
that `log Z(0) = log 1 = 0` once `Z` is normalized by its own zeroth-order value. -/
theorem constantCoeff_formalLogPartitionFunction {Z : PowerSeries ℂ}
    (hZ : constantCoeff Z = 1) : constantCoeff (formalLogPartitionFunction Z) = 0 := by
  rw [formalLogPartitionFunction, ← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_subst' (hasSubst_sub_one_of_constantCoeff_eq_one hZ)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hZ1 : constantCoeff (Z - 1) = 0 := by simp [hZ]
    have : PowerSeries.coeff 0 ((Z - 1) ^ d) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hZ1, zero_pow hd.ne']
    simp [this]

/-- **The order-`1` coefficient of `log Z` equals the order-`1` coefficient of `Z` itself.**
Standard first-order fact for `log(1+X)`: the connected and disconnected pictures only start to
differ from second order onward. -/
@[simp]
theorem coeff_one_formalLogPartitionFunction {Z : PowerSeries ℂ} (hZ : constantCoeff Z = 1) :
    PowerSeries.coeff 1 (formalLogPartitionFunction Z) = PowerSeries.coeff 1 Z := by
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
      rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hZ1
    rw [Finset.sum_insert (by decide), Finset.sum_singleton, hcoeff0', hcoeff0]
    ring
  have hterm : ∀ d : ℕ, d ≠ 1 →
      PowerSeries.coeff d (log ℂ) • PowerSeries.coeff 1 ((Z - 1) ^ d) = 0 := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · simp
    · simp [hpow d (by omega)]
  rw [formalLogPartitionFunction, coeff_subst' (hasSubst_sub_one_of_constantCoeff_eq_one hZ),
    finsum_eq_single _ 1 hterm, coeff_one_log, one_smul, pow_one, map_sub, PowerSeries.coeff_one]
  simp

end SecondQuantization
