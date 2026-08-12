import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.IrreducibleDef

set_option linter.style.header false

/-!
# Formal exponential and logarithm helpers

Mathlib already provides the canonical formal substitution inverse of a power series with zero
constant coefficient and invertible linear coefficient. Since `PowerSeries.log ℂ` satisfies those
hypotheses, its substitution inverse is the formal series `exp(X) - 1` without requiring a separate
project-local proof of the scalar exp/log inverse identities.

This module packages that inverse into the normalized formal exponential used by linked-cluster
consumers. The public wrapper is irreducible so Lean does not unfold the large substitution-inverse
construction during unification.
-/

namespace PowerSeries

private theorem coeff_one_log_isUnit : IsUnit (PowerSeries.coeff 1 (PowerSeries.log ℂ)) := by
  simp

private noncomputable def expSubOne : PowerSeries ℂ :=
  (PowerSeries.log ℂ).substInvOfIsUnit coeff_one_log_isUnit

@[simp]
private theorem constantCoeff_expSubOne : PowerSeries.constantCoeff expSubOne = 0 := by
  simp [expSubOne]

private theorem log_subst_expSubOne :
    (PowerSeries.log ℂ).subst expSubOne = PowerSeries.X := by
  exact PowerSeries.subst_substInvOfIsUnit_right
    (PowerSeries.log ℂ) (by simp) coeff_one_log_isUnit

/-- Formal exponential of a zero-based series. It is `1` plus substitution into the canonical
formal inverse of `log(1 + X)`. The definition is irreducible to keep the substitution-inverse
implementation out of unification. -/
noncomputable irreducible_def formalExp (C : PowerSeries ℂ) : PowerSeries ℂ :=
  1 + expSubOne.subst C

/-- The formal exponential of a zero-constant-coefficient series has constant coefficient one. -/
theorem constantCoeff_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.constantCoeff (formalExp C) = 1 := by
  rw [formalExp]
  have htail : PowerSeries.constantCoeff (expSubOne.subst C) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hC expSubOne constantCoeff_expSubOne
  simp [htail]

set_option maxHeartbeats 800000 in
/-- `logOf` is a left inverse of the formal exponential on zero-constant-coefficient series. -/
theorem logOf_formalExp {C : PowerSeries ℂ}
    (hC : PowerSeries.constantCoeff C = 0) :
    PowerSeries.logOf (formalExp C) = C := by
  have hCsub : PowerSeries.HasSubst C :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hC
  have hEsub : PowerSeries.HasSubst expSubOne :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_expSubOne
  rw [formalExp, PowerSeries.logOf_eq]
  have htail : (1 + expSubOne.subst C : PowerSeries ℂ) - 1 = expSubOne.subst C := by
    ring
  rw [htail]
  have hcomp :
      ((PowerSeries.log ℂ).subst expSubOne).subst C =
        (PowerSeries.log ℂ).subst (expSubOne.subst C) :=
    PowerSeries.subst_comp_subst_apply (R := ℂ) (S := ℂ) (T := ℂ)
      hEsub hCsub (PowerSeries.log ℂ)
  calc
    (PowerSeries.log ℂ).subst (expSubOne.subst C) =
        ((PowerSeries.log ℂ).subst expSubOne).subst C := hcomp.symm
    _ = PowerSeries.X.subst C := by rw [log_subst_expSubOne]
    _ = C := PowerSeries.subst_X hCsub

end PowerSeries
