import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Algebra of the formal logarithm

This file records the multiplicative laws of `PowerSeries.logOf` needed by linked-cluster and
thermal grand-partition consumers. The statements are purely formal and require only normalized
constant coefficient `1`; no analytic convergence or evaluation is involved.
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

/-- Logarithmic derivative identity for a normalized complex power series. -/
theorem derivative_logOf_mul {Z : PowerSeries ℂ}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX ℂ (PowerSeries.logOf Z) * Z = d⁄dX ℂ Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries ℂ => f.subst (Z - 1))
    derivative_log_mul_one_add_X
  have hone : (1 : PowerSeries ℂ).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries ℂ) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst ℂ hsub]
  have hderiv : d⁄dX ℂ (Z - 1) = d⁄dX ℂ Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * d⁄dX ℂ Z) * Z =
        ((d⁄dX ℂ (PowerSeries.log ℂ)).subst (Z - 1) * Z) * d⁄dX ℂ Z := by
          ring
    _ = d⁄dX ℂ Z := by rw [hgeom']; simp

/-- The formal logarithm turns products of normalized complex power series into sums. -/
theorem logOf_mul {F G : PowerSeries ℂ}
    (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.constantCoeff G = 1) :
    PowerSeries.logOf (F * G) = PowerSeries.logOf F + PowerSeries.logOf G := by
  have hFG : PowerSeries.constantCoeff (F * G) = 1 := by simp [hF, hG]
  apply PowerSeries.derivative.ext
  · change d⁄dX ℂ (PowerSeries.logOf (F * G)) =
      d⁄dX ℂ (PowerSeries.logOf F) + d⁄dX ℂ (PowerSeries.logOf G)
    have hleft := derivative_logOf_mul hFG
    have hFlog := derivative_logOf_mul hF
    have hGlog := derivative_logOf_mul hG
    have hright :
        (d⁄dX ℂ (PowerSeries.logOf F) + d⁄dX ℂ (PowerSeries.logOf G)) * (F * G) =
          d⁄dX ℂ (F * G) := by
      calc
        (d⁄dX ℂ (PowerSeries.logOf F) + d⁄dX ℂ (PowerSeries.logOf G)) * (F * G) =
            (d⁄dX ℂ (PowerSeries.logOf F) * F) * G +
              F * (d⁄dX ℂ (PowerSeries.logOf G) * G) := by ring
        _ = d⁄dX ℂ F * G + F * d⁄dX ℂ G := by rw [hFlog, hGlog]
        _ = d⁄dX ℂ (F * G) := by
          simpa [smul_eq_mul, add_comm, mul_comm] using
            ((PowerSeries.derivative ℂ).leibniz F G).symm
    have hne : (F * G) ≠ 0 := by
      intro hzero
      have := congrArg PowerSeries.constantCoeff hzero
      simp [hFG] at this
    exact mul_right_cancel₀ hne (hleft.trans hright.symm)
  · rw [PowerSeries.constantCoeff_logOf hFG, map_add,
      PowerSeries.constantCoeff_logOf hF, PowerSeries.constantCoeff_logOf hG]
    simp

/-- The formal logarithm of one is zero. -/
@[simp]
theorem logOf_one : PowerSeries.logOf (1 : PowerSeries ℂ) = 0 := by
  apply PowerSeries.derivative.ext
  · have h := derivative_logOf_mul (Z := (1 : PowerSeries ℂ)) (by simp)
    simpa using h
  · rw [PowerSeries.constantCoeff_logOf (by simp)]
    simp

/-- The formal logarithm of the inverse of a normalized complex power series is the negative
formal logarithm. -/
theorem logOf_inv {F : PowerSeries ℂ}
    (hF : PowerSeries.constantCoeff F = 1) :
    PowerSeries.logOf F⁻¹ = -PowerSeries.logOf F := by
  have hFinv : PowerSeries.constantCoeff F⁻¹ = 1 := by simp [hF]
  have hmul := logOf_mul hF hFinv
  have hF0 : PowerSeries.constantCoeff F ≠ 0 := by simp [hF]
  rw [PowerSeries.mul_inv_cancel F hF0, logOf_one] at hmul
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hmul.symm)

end PowerSeries
