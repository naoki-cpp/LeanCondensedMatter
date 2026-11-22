import LeanCondensedMatter.Transport.Disorder.TMatrix
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Scalar-impurity T-matrix norm bound

An algebraic T-matrix fixed-point identity and its scalar inverse-shift
representation imply a quadratic bound on the bare-potential remainder.
No Hamiltonian, matrix dimension, or disorder ensemble is fixed.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- The remainder of a scalar-impurity T-matrix carries two powers of its
strength, given its exact fixed-point equation and inverse-shift factorization. -/
theorem scalarImpurityRemainder_norm_le
    (strength : ℂ) (greenLoop inverseShift tMatrix : R)
    (hfixed : tMatrix - strength • (1 : R) =
      strength • (greenLoop * tMatrix))
    (ht : tMatrix = strength • inverseShift) :
    ‖tMatrix - strength • (1 : R)‖ ≤
      ‖strength‖ ^ 2 * ‖greenLoop‖ * ‖inverseShift‖ := by
  rw [hfixed, norm_smul]
  calc
    ‖strength‖ * ‖greenLoop * tMatrix‖ ≤
        ‖strength‖ * (‖greenLoop‖ * ‖tMatrix‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖strength‖ ^ 2 * ‖greenLoop‖ * ‖inverseShift‖ := by
      rw [ht, norm_smul]
      ring

end

end QuantumTheory.Transport
