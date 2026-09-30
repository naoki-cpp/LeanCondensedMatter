import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Log

set_option linter.style.header false

/-!
# Algebra of the formal logarithm

This file records the multiplicative laws of `PowerSeries.logOf` needed by linked-cluster and
thermal grand-partition consumers. The statements are purely formal and require only normalized
constant coefficient `1`; no analytic convergence or evaluation is involved.
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

/-- The formal logarithm of a normalized linear factor is the corresponding rescaled scalar
`log(1 + X)` series. -/
theorem logOf_one_add_smul_X (q : ℂ) :
    PowerSeries.logOf (1 + q • PowerSeries.X) =
      PowerSeries.rescale q (PowerSeries.log ℂ) := by
  rw [PowerSeries.logOf_eq]
  have htail : (1 + q • PowerSeries.X : PowerSeries ℂ) - 1 = q • PowerSeries.X := by
    ring
  rw [htail, PowerSeries.rescale_eq_subst]

/-- `logOf` turns a finite product of normalized complex power series into the corresponding finite
sum. -/
theorem logOf_finset_prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ)
    (hF : ∀ i, PowerSeries.constantCoeff (F i) = 1) :
    PowerSeries.logOf (∏ i ∈ s, F i) = ∑ i ∈ s, PowerSeries.logOf (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [PowerSeries.logOf_mul (hF a) (by simp [hF])]
      rw [ih]

end PowerSeries
