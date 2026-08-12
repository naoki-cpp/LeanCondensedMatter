import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Formal exponential and logarithm helpers

This file supplies the small statistics-independent formal power-series API needed by thermal
exchange consumers. Mathlib owns the scalar `exp`, `log`, substitution, and derivative machinery;
this module packages substitution of `exp` and proves the inverse laws against `PowerSeries.logOf`.
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

/-- `log(1 + X)` and `exp(X) - 1` are inverse under formal substitution. -/
theorem log_subst_exp_sub_one :
    (PowerSeries.log ℂ).subst (PowerSeries.exp ℂ - 1) = PowerSeries.X := by
  let g : PowerSeries ℂ := PowerSeries.exp ℂ - 1
  have hg : PowerSeries.HasSubst g := by
    dsimp [g]
    exact PowerSeries.HasSubst.exp_sub_one
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_subst ℂ hg, PowerSeries.derivative_X]
    have hderivg : d⁄dX ℂ g = PowerSeries.exp ℂ := by
      dsimp [g]
      simp [PowerSeries.derivative_exp]
    rw [hderivg]
    have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst g)
      derivative_log_mul_one_add_X
    rw [PowerSeries.subst_mul hg, PowerSeries.subst_add hg] at hgeom
    simpa [g, PowerSeries.subst_X hg] using hgeom
  · have hg0 : PowerSeries.constantCoeff g = 0 := by
      simp [g]
    rw [PowerSeries.constantCoeff_X]
    exact PowerSeries.constantCoeff_subst_eq_zero hg0 (PowerSeries.log ℂ)
      PowerSeries.constantCoeff_log

/-- The converse scalar substitution identity: `exp(log(1 + X)) - 1 = X`. -/
theorem exp_sub_one_subst_log :
    (PowerSeries.exp ℂ - 1).subst (PowerSeries.log ℂ) = PowerSeries.X := by
  let P : PowerSeries ℂ := PowerSeries.log ℂ
  let E : PowerSeries ℂ := PowerSeries.exp ℂ - 1
  have hP0 : PowerSeries.constantCoeff P = 0 := by simp [P]
  have hP1 : IsUnit (PowerSeries.coeff 1 P) := by simp [P]
  have hPsub : PowerSeries.HasSubst P := by
    dsimp [P]
    exact PowerSeries.HasSubst.log
  have hEsub : PowerSeries.HasSubst E := by
    dsimp [E]
    exact PowerSeries.HasSubst.exp_sub_one
  let Q : PowerSeries ℂ := P.substInvOfIsUnit hP1
  have hQleft : Q.subst P = PowerSeries.X := by
    dsimp [Q]
    exact PowerSeries.subst_substInvOfIsUnit_left P hP0 hP1
  have hPE : P.subst E = PowerSeries.X := by
    simpa [P, E] using log_subst_exp_sub_one
  have hEeqQ : E = Q := by
    calc
      E = PowerSeries.X.subst E := (PowerSeries.subst_X hEsub).symm
      _ = (Q.subst P).subst E := by rw [hQleft]
      _ = Q.subst (P.subst E) := by
        exact PowerSeries.subst_comp_subst_apply hPsub hEsub Q
      _ = Q.subst PowerSeries.X := by rw [hPE]
      _ = Q := PowerSeries.X_subst Q
  rw [show PowerSeries.exp ℂ - 1 = E by rfl, hEeqQ, hQleft]

/-- Substituting the formal logarithm into the scalar exponential gives `1 + X`. -/
theorem exp_subst_log_eq_one_add_X :
    (PowerSeries.exp ℂ).subst (PowerSeries.log ℂ) = 1 + PowerSeries.X := by
  have hlog : PowerSeries.HasSubst (PowerSeries.log ℂ) := PowerSeries.HasSubst.log
  have h := exp_sub_one_subst_log
  rw [PowerSeries.subst_sub hlog] at h
  simp at h
  simpa [add_comm] using (sub_eq_iff_eq_add.mp h)

/-- Formal exponential of a series, defined by substituting it into Mathlib's scalar exponential
series. The inverse laws below use the natural zero/one constant-coefficient boundaries. -/
noncomputable def formalExp (C : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst C

/-- The formal exponential of a zero-constant-coefficient series has constant coefficient one. -/
theorem constantCoeff_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.constantCoeff (formalExp C) = 1 := by
  have hsubst : PowerSeries.HasSubst C :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hC
  have htail :
      PowerSeries.constantCoeff ((PowerSeries.exp ℂ - 1).subst C) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hC (PowerSeries.exp ℂ - 1) (by simp)
  have hexp :
      formalExp C = 1 + (PowerSeries.exp ℂ - 1).subst C := by
    rw [formalExp, show PowerSeries.exp ℂ = 1 + (PowerSeries.exp ℂ - 1) by ring]
    rw [PowerSeries.subst_add hsubst]
    simp
  rw [hexp, map_add, map_one, htail, add_zero]

/-- `logOf` is a left inverse of the formal exponential on zero-constant-coefficient series. -/
theorem logOf_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.logOf (formalExp C) = C := by
  have hsubst : PowerSeries.HasSubst C :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hC
  rw [PowerSeries.logOf_eq]
  have htail :
      formalExp C - 1 = (PowerSeries.exp ℂ - 1).subst C := by
    rw [formalExp, PowerSeries.subst_sub hsubst]
    simp
  rw [htail]
  calc
    (PowerSeries.log ℂ).subst ((PowerSeries.exp ℂ - 1).subst C) =
        ((PowerSeries.log ℂ).subst (PowerSeries.exp ℂ - 1)).subst C := by
      symm
      exact PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.exp_sub_one hsubst
        (PowerSeries.log ℂ)
    _ = PowerSeries.X.subst C := by rw [log_subst_exp_sub_one]
    _ = C := PowerSeries.subst_X hsubst

/-- Formal exponential is a left inverse of `logOf` on one-constant-coefficient series. -/
theorem formalExp_logOf {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    formalExp (PowerSeries.logOf Z) = Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hlog : PowerSeries.HasSubst (PowerSeries.log ℂ) := PowerSeries.HasSubst.log
  rw [formalExp, PowerSeries.logOf_eq]
  calc
    (PowerSeries.exp ℂ).subst ((PowerSeries.log ℂ).subst (Z - 1)) =
        ((PowerSeries.exp ℂ).subst (PowerSeries.log ℂ)).subst (Z - 1) := by
      symm
      exact PowerSeries.subst_comp_subst_apply hlog hsub (PowerSeries.exp ℂ)
    _ = (1 + PowerSeries.X).subst (Z - 1) := by rw [exp_subst_log_eq_one_add_X]
    _ = 1 + (Z - 1) := by
      rw [PowerSeries.subst_add hsub, PowerSeries.subst_X hsub]
      simp
    _ = Z := by ring

end PowerSeries
