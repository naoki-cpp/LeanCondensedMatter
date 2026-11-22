import LeanCondensedMatter.Transport.Disorder.TMatrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar-impurity T-matrix norm bound

The exact T-matrix fixed-point relation bounds the correction beyond the bare
impurity by two powers of its strength in any complex normed algebra.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- A scalar impurity with a unit shift has a quadratic bare-potential remainder.
The bound keeps the full inverse-shift norm without a Born approximation. -/
theorem norm_scalarImpurityTMatrix_sub_bare_le
    (strength : ℂ) (greenLoop : R)
    (hinvertible : IsUnit (1 - strength • greenLoop)) :
    ‖scalarImpurityTMatrix strength greenLoop hinvertible - strength • (1 : R)‖ ≤
      ‖strength‖ ^ 2 * ‖greenLoop‖ * ‖(↑(hinvertible.unit⁻¹) : R)‖ := by
  rw [scalarImpurityTMatrix_sub_bare, norm_smul]
  calc
    ‖strength‖ * ‖greenLoop * scalarImpurityTMatrix strength greenLoop hinvertible‖ ≤
        ‖strength‖ * (‖greenLoop‖ * ‖scalarImpurityTMatrix strength greenLoop hinvertible‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖strength‖ ^ 2 * ‖greenLoop‖ * ‖(↑(hinvertible.unit⁻¹) : R)‖ := by
      rw [scalarImpurityTMatrix, norm_smul]
      ring

end

end QuantumTheory.Transport
