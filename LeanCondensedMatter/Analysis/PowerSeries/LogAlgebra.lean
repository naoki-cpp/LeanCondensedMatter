import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Algebra of the formal logarithm

This file records the formal logarithmic derivative identity and the logarithm's product law
for normalized power series. Both are algebraic and require no analytic convergence.
-/

open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Logarithmic derivative identity for a normalized power series over a rational algebra. -/
theorem derivative_logOf_mul {Z : PowerSeries R}
    (hZ : PowerSeries.constantCoeff Z = 1) :
    d⁄dX (PowerSeries.logOf Z) * Z = d⁄dX Z := by
  have hsub : PowerSeries.HasSubst (Z - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hZ])
  have hgeom := congrArg (fun f : PowerSeries R => f.subst (Z - 1))
    derivative_log_mul_one_add_X
  have hone : (1 : PowerSeries R).subst (Z - 1) = 1 := by
    rw [show (1 : PowerSeries R) = PowerSeries.C 1 by rfl, PowerSeries.subst_C]
    rfl
  have hgeom' :
      (d⁄dX (PowerSeries.log R)).subst (Z - 1) * Z = 1 := by
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub,
      PowerSeries.subst_X hsub, hone] at hgeom
    simpa using hgeom
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsub]
  have hderiv : d⁄dX (Z - 1) = d⁄dX Z := by simp
  rw [hderiv]
  calc
    ((d⁄dX (PowerSeries.log R)).subst (Z - 1) * d⁄dX Z) * Z =
        ((d⁄dX (PowerSeries.log R)).subst (Z - 1) * Z) * d⁄dX Z := by
          ring
    _ = d⁄dX Z := by rw [hgeom']; simp

/-- The formal logarithm turns products of normalized complex power series into sums. -/
theorem logOf_mul {F G : PowerSeries ℂ}
    (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.constantCoeff G = 1) :
    PowerSeries.logOf (F * G) = PowerSeries.logOf F + PowerSeries.logOf G := by
  have hFG : PowerSeries.constantCoeff (F * G) = 1 := by simp [hF, hG]
  apply PowerSeries.derivative.ext
  · rw [map_add]
    have hleft := derivative_logOf_mul hFG
    have hFlog := derivative_logOf_mul hF
    have hGlog := derivative_logOf_mul hG
    have hright :
        (d⁄dX (PowerSeries.logOf F) + d⁄dX (PowerSeries.logOf G)) * (F * G) =
          d⁄dX (F * G) := by
      calc
        (d⁄dX (PowerSeries.logOf F) + d⁄dX (PowerSeries.logOf G)) * (F * G) =
            (d⁄dX (PowerSeries.logOf F) * F) * G +
              F * (d⁄dX (PowerSeries.logOf G) * G) := by ring
        _ = d⁄dX F * G + F * d⁄dX G := by rw [hFlog, hGlog]
        _ = d⁄dX (F * G) := by
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

end PowerSeries
