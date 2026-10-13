import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import Mathlib.Tactic

set_option linter.style.header false

/-!
# In-plane spinor rotation of the massive-Dirac Pauli matrix

The isotropic two-dimensional Dirac operator is covariant under a rotation of
momentum together with a diagonal two-band basis transformation. The chosen
spinor matrix differs from the usual SU(2) half-angle rotation by a scalar
phase, which cancels in conjugation. Its entries avoid square roots and work
directly with the existing complex Pauli representation.

The identities below are algebraic, not a claim that a disorder-averaged
crossed-current block or real-space trace has already been rotated.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

/-- Diagonal spinor representative of an in-plane rotation through `angle`. -/
def inPlaneSpinRotation (angle : ℝ) : Matrix2 :=
  !![1, 0;
     0, (((Real.cos angle : ℝ) : ℂ) + Complex.I * ((Real.sin angle : ℝ) : ℂ))]

/-- Explicit inverse spinor rotation. -/
def inPlaneSpinRotationInverse (angle : ℝ) : Matrix2 :=
  !![1, 0;
     0, (((Real.cos angle : ℝ) : ℂ) - Complex.I * ((Real.sin angle : ℝ) : ℂ))]

private theorem inPlaneSpinRotation_phases_mul (angle : ℝ) :
    ((((Real.cos angle : ℝ) : ℂ) + Complex.I * ((Real.sin angle : ℝ) : ℂ)) *
      (((Real.cos angle : ℝ) : ℂ) - Complex.I * ((Real.sin angle : ℝ) : ℂ))) = 1 := by
  have htrig :
      (((Real.cos angle : ℝ) : ℂ) ^ 2) +
        (((Real.sin angle : ℝ) : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq angle
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  calc
    _ = (((Real.cos angle : ℝ) : ℂ) ^ 2) +
        (((Real.sin angle : ℝ) : ℂ) ^ 2) := by
      calc
        _ = (((Real.cos angle : ℝ) : ℂ) ^ 2) -
            Complex.I ^ 2 * (((Real.sin angle : ℝ) : ℂ) ^ 2) := by ring
        _ = _ := by rw [hI]; ring
    _ = 1 := htrig

/-- The spinor rotations are mutual inverses. -/
theorem inPlaneSpinRotation_mul_inverse (angle : ℝ) :
    inPlaneSpinRotation angle * inPlaneSpinRotationInverse angle = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two, inPlaneSpinRotation_phases_mul]

/-- The inverse spinor can also be placed on the left. -/
theorem inPlaneSpinRotationInverse_mul (angle : ℝ) :
    inPlaneSpinRotationInverse angle * inPlaneSpinRotation angle = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two, mul_comm,
      inPlaneSpinRotation_phases_mul]

/-- Rotating the Pauli-x axis produces the polar in-plane Pauli direction. -/
theorem inPlaneSpinRotation_sigmaX (angle : ℝ) :
    inPlaneSpinRotation angle * sigmaX * inPlaneSpinRotationInverse angle =
      (((Real.cos angle : ℝ) : ℂ)) • sigmaX +
        (((Real.sin angle : ℝ) : ℂ)) • sigmaY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sigmaX, sigmaY,
      InternalSpace.pauliX, InternalSpace.pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [Complex.I_mul_I]
  all_goals ring

/-- Rotating the Pauli-y axis gives its oriented orthogonal partner. -/
theorem inPlaneSpinRotation_sigmaY (angle : ℝ) :
    inPlaneSpinRotation angle * sigmaY * inPlaneSpinRotationInverse angle =
      -(((Real.sin angle : ℝ) : ℂ)) • sigmaX +
        (((Real.cos angle : ℝ) : ℂ)) • sigmaY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sigmaX, sigmaY,
      InternalSpace.pauliX, InternalSpace.pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [Complex.I_mul_I]
  all_goals ring

/-- The mass Pauli axis is invariant under in-plane spinor rotation. -/
theorem inPlaneSpinRotation_sigmaZ (angle : ℝ) :
    inPlaneSpinRotation angle * sigmaZ * inPlaneSpinRotationInverse angle = sigmaZ := by
  have hcomm :
      inPlaneSpinRotation angle * sigmaZ = sigmaZ * inPlaneSpinRotation angle := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [inPlaneSpinRotation, sigmaZ, InternalSpace.pauliZ,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hcomm, ← mul_assoc, inPlaneSpinRotation_mul_inverse, mul_one]

/-- Polar Pauli matrices are conjugate to their radial-axis specialization
under the physical in-plane spinor rotation. -/
theorem polarPauliMatrix_eq_spinRotation (a b d : ℂ) (angle : ℝ) :
    polarPauliMatrix a b d angle =
      inPlaneSpinRotation angle * polarPauliMatrix a b d 0 *
        inPlaneSpinRotationInverse angle := by
  simp only [polarPauliMatrix, Real.cos_zero, Real.sin_zero]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul,
    zero_smul, add_zero]
  rw [mul_add, mul_add, add_mul, add_mul]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [← mul_assoc, inPlaneSpinRotation_mul_inverse]
  simp

end

end QuantumTheory.Models.MassiveDirac
