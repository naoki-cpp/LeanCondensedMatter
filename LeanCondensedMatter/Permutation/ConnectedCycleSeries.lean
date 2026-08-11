import LeanCondensedMatter.Permutation.CycleEGF
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# Formal connected-cycle series

This file packages the W3 connected coefficients into a scalar formal power series. The matrix
kernel remains inside the coefficients through `trace (K ^ m)`; the power-series coefficient ring
is `ℂ`, so no commutativity assumption is imposed on the matrix algebra itself.
-/

namespace Combinatorics

variable {ι : Type*} [Fintype ι]

/-- The formal connected-cycle series associated with exchange weight `ζ` and finite kernel `K`.

Its constant coefficient is zero. At positive order `m`, its coefficient is the EGF-normalized
assignment-summed one-cycle contribution. -/
noncomputable def permutationConnectedCycleSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (assignmentSingleCycleEGFCoeff ζ K)

@[simp]
theorem coeff_permutationConnectedCycleSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) :
    PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
      assignmentSingleCycleEGFCoeff ζ K m :=
  PowerSeries.coeff_mk m _

@[simp]
theorem constantCoeff_permutationConnectedCycleSeries
    (ζ : ℂ) (K : Matrix ι ι ℂ) :
    PowerSeries.constantCoeff (permutationConnectedCycleSeries ζ K) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_permutationConnectedCycleSeries]
  exact assignmentSingleCycleEGFCoeff_zero ζ K

/-- Positive coefficients of the formal connected-cycle series are the universal cyclic trace
coefficients `ζ^(m-1) tr(K^m) / m`. -/
theorem coeff_permutationConnectedCycleSeries_of_pos
    [DecidableEq ι] (ζ : ℂ) (K : Matrix ι ι ℂ) (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m (permutationConnectedCycleSeries ζ K) =
      ζ ^ (m - 1) * Matrix.trace (K ^ m) / (m : ℂ) := by
  rw [coeff_permutationConnectedCycleSeries]
  exact assignmentSingleCycleEGFCoeff_eq_pow_mul_trace_div ζ K m hm

/-- Coefficientwise closed form for the connected-cycle series, including the zero-order term. -/
theorem permutationConnectedCycleSeries_eq_mk_trace
    [DecidableEq ι] (ζ : ℂ) (K : Matrix ι ι ℂ) :
    permutationConnectedCycleSeries ζ K =
      PowerSeries.mk (fun m =>
        if m = 0 then 0
        else ζ ^ (m - 1) * Matrix.trace (K ^ m) / (m : ℂ)) := by
  ext m
  rw [coeff_permutationConnectedCycleSeries, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst m
    simp
  · rw [assignmentSingleCycleEGFCoeff_eq_pow_mul_trace_div ζ K m (Nat.pos_of_ne_zero hm)]
    simp [hm]

/-- The `ζ = 0` boundary is handled coefficientwise without dividing by `ζ`: only the linear
coefficient survives. -/
theorem coeff_permutationConnectedCycleSeries_zero_exchange
    (K : Matrix ι ι ℂ) (m : ℕ) :
    PowerSeries.coeff m (permutationConnectedCycleSeries 0 K) =
      if m = 1 then Matrix.trace K else 0 := by
  classical
  cases m with
  | zero => simp
  | succ n =>
      cases n with
      | zero =>
          rw [coeff_permutationConnectedCycleSeries_of_pos (0 : ℂ) K 1 (by omega)]
          simp
      | succ n =>
          rw [coeff_permutationConnectedCycleSeries_of_pos (0 : ℂ) K (n + 2) (by omega)]
          simp

end Combinatorics
