import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal exponential and logarithm helpers

This file supplies the small statistics-independent formal power-series API needed by thermal
exchange consumers. Mathlib owns the scalar `exp`, `log`, substitution, and derivative machinery;
this module packages substitution of `exp` and proves the inverse law needed by the linked-cluster
consumer.
-/

namespace PowerSeries

/-- The derivative of `log(1 + X)` multiplied by `1 + X` is one. -/
theorem derivative_log_mul_one_add_X :
    d⁄dX ℂ (PowerSeries.log ℂ) * (1 + PowerSeries.X) = 1 := by
  rw [PowerSeries.deriv_log, mul_add, mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_mk, pow_succ]

/-- `log(1 + X)` is a left substitution inverse of `exp(X) - 1`. -/
theorem log_subst_exp_sub_one :
    (PowerSeries.log ℂ).subst (PowerSeries.exp ℂ - 1) = PowerSeries.X := by
  let g : PowerSeries ℂ := PowerSeries.exp ℂ - 1
  have hg : PowerSeries.HasSubst g := by
    dsimp [g]
    exact PowerSeries.HasSubst.exp_sub_one
  have hone : (1 : PowerSeries ℂ).subst g = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst ℂ hg, PowerSeries.derivative_X]
    have hderivg : d⁄dX ℂ g = PowerSeries.exp ℂ := by
      dsimp [g]
      simp [PowerSeries.derivative_exp]
    rw [hderivg]
    have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst g)
      derivative_log_mul_one_add_X
    rw [PowerSeries.subst_mul hg, PowerSeries.subst_add hg,
      PowerSeries.subst_X hg, hone] at hgeom
    have hsum : (1 : PowerSeries ℂ) + g = PowerSeries.exp ℂ := by
      dsimp [g]
      ring
    rw [hsum] at hgeom
    exact hgeom
  · have hg0 : PowerSeries.constantCoeff g = 0 := by
      simp [g]
    rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero hg0 (PowerSeries.log ℂ)
      PowerSeries.constantCoeff_log

/-- Formal exponential of a series, defined by substituting it into Mathlib's scalar exponential
series. The inverse law below uses the natural zero-constant-coefficient boundary. -/
noncomputable def formalExp (C : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst C

private theorem formalExp_eq_one_add_tail {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    formalExp C = 1 + (PowerSeries.exp ℂ - 1).subst C := by
  have hsubst : PowerSeries.HasSubst C :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hC
  have hone : (1 : PowerSeries ℂ).subst C = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hsplit :
      (PowerSeries.exp ℂ : PowerSeries ℂ) = 1 + (PowerSeries.exp ℂ - 1) := by
    ring
  have h := congrArg (fun f : PowerSeries ℂ => f.subst C) hsplit
  rw [PowerSeries.subst_add hsubst, hone] at h
  exact h

/-- The formal exponential of a zero-constant-coefficient series has constant coefficient one. -/
theorem constantCoeff_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.constantCoeff (formalExp C) = 1 := by
  rw [formalExp_eq_one_add_tail hC, map_add, map_one]
  have htail :
      PowerSeries.constantCoeff ((PowerSeries.exp ℂ - 1).subst C) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hC (PowerSeries.exp ℂ - 1) (by simp)
  rw [htail, add_zero]

/-- `logOf` is a left inverse of the formal exponential on zero-constant-coefficient series. -/
theorem logOf_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.logOf (formalExp C) = C := by
  have hsubst : PowerSeries.HasSubst C :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hC
  rw [PowerSeries.logOf_eq]
  have htail :
      formalExp C - 1 = (PowerSeries.exp ℂ - 1).subst C := by
    rw [formalExp_eq_one_add_tail hC]
    ring
  rw [htail]
  calc
    (PowerSeries.log ℂ).subst ((PowerSeries.exp ℂ - 1).subst C) =
        ((PowerSeries.log ℂ).subst (PowerSeries.exp ℂ - 1)).subst C := by
      exact (PowerSeries.subst_comp_subst_apply
        PowerSeries.HasSubst.exp_sub_one hsubst (PowerSeries.log ℂ)).symm
    _ = PowerSeries.X.subst C := by rw [log_subst_exp_sub_one]
    _ = C := PowerSeries.subst_X hsubst

end PowerSeries
