import Mathlib.Algebra.Algebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Scalar-potential T-matrix algebra

The impurity potential is a scalar multiple of the identity in an arbitrary (possibly
noncommutative) complex algebra. A supplied Green loop need not commute with other
operators. Invertibility of `1 - v • G` is an explicit assumption; no Born approximation,
geometric-series convergence, thermodynamic limit, or disorder ensemble is implied.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Scalar-impurity T-matrix `v (1 - v G)⁻¹`, defined for a unit shift. -/
noncomputable def scalarImpurityTMatrix
    (strength : ℂ) (greenLoop : R)
    (hinvertible : IsUnit (1 - strength • greenLoop)) : R :=
  strength • (↑(hinvertible.unit⁻¹) : R)

/-- The shifted T-matrix reproduces the bare scalar potential. -/
theorem scalarImpurityShift_mul_tMatrix
    (strength : ℂ) (greenLoop : R)
    (hinvertible : IsUnit (1 - strength • greenLoop)) :
    (1 - strength • greenLoop) *
      scalarImpurityTMatrix strength greenLoop hinvertible = strength • (1 : R) := by
  unfold scalarImpurityTMatrix
  rw [mul_smul_comm, hinvertible.mul_val_inv]

/-- Exact Lippmann–Schwinger equation `T = vI + vGT`; invertibility alone suffices. -/
theorem scalarImpurityTMatrix_fixedPoint
    (strength : ℂ) (greenLoop : R)
    (hinvertible : IsUnit (1 - strength • greenLoop)) :
    scalarImpurityTMatrix strength greenLoop hinvertible =
      strength • (1 : R) +
        strength • (greenLoop * scalarImpurityTMatrix strength greenLoop hinvertible) := by
  have h := scalarImpurityShift_mul_tMatrix strength greenLoop hinvertible
  simp only [sub_mul, one_mul, smul_mul_assoc] at h
  exact (sub_eq_iff_eq_add).mp h

/-- The exact correction beyond the bare impurity is `T - vI = vGT`. -/
theorem scalarImpurityTMatrix_sub_bare
    (strength : ℂ) (greenLoop : R)
    (hinvertible : IsUnit (1 - strength • greenLoop)) :
    scalarImpurityTMatrix strength greenLoop hinvertible - strength • (1 : R) =
      strength • (greenLoop * scalarImpurityTMatrix strength greenLoop hinvertible) := by
  have hfixed := scalarImpurityTMatrix_fixedPoint strength greenLoop hinvertible
  calc
    _ = (strength • (1 : R) +
          strength • (greenLoop * scalarImpurityTMatrix strength greenLoop hinvertible)) -
          strength • (1 : R) :=
      congrArg (fun x : R => x - strength • (1 : R)) hfixed
    _ = _ := by abel

end
end Transport
end QuantumTheory
