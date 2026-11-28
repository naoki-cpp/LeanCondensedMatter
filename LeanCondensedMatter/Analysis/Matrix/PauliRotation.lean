import LeanCondensedMatter.Analysis.Matrix.Pauli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# In-plane rotations of Pauli matrices

The diagonal spinor representative of a planar rotation differs from the
SU(2) half-angle representative by a scalar phase that cancels in conjugation.
This module owns its inverse, entrywise action, action on the Pauli basis,
and the corresponding polar Pauli matrix and sandwich identities.
-/

namespace InternalSpace

noncomputable section

/-- Diagonal spinor representative of an in-plane rotation through `angle`. -/
def inPlaneSpinRotation (angle : ℝ) : PauliMatrix :=
  !![1, 0;
     0, (((Real.cos angle : ℝ) : ℂ) + Complex.I * ((Real.sin angle : ℝ) : ℂ))]

/-- Explicit inverse spinor rotation. -/
def inPlaneSpinRotationInverse (angle : ℝ) : PauliMatrix :=
  !![1, 0;
     0, (((Real.cos angle : ℝ) : ℂ) - Complex.I * ((Real.sin angle : ℝ) : ℂ))]

private theorem inPlaneSpinRotation_phases_mul (angle : ℝ) :
    ((((Real.cos angle : ℝ) : ℂ) + Complex.I * ((Real.sin angle : ℝ) : ℂ)) *
      (((Real.cos angle : ℝ) : ℂ) - Complex.I * ((Real.sin angle : ℝ) : ℂ))) = 1 := by
  have htrig :
      (((Real.cos angle : ℝ) : ℂ) ^ 2) +
        (((Real.sin angle : ℝ) : ℂ) ^ 2) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq angle
  calc
    _ = (((Real.cos angle : ℝ) : ℂ) ^ 2) -
        Complex.I ^ 2 * (((Real.sin angle : ℝ) : ℂ) ^ 2) := by ring
    _ = 1 := by rw [Complex.I_sq, ← htrig]; ring

/-- The spinor rotations are mutual inverses. -/
theorem inPlaneSpinRotation_mul_inverse (angle : ℝ) :
    inPlaneSpinRotation angle * inPlaneSpinRotationInverse angle = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two]
  exact inPlaneSpinRotation_phases_mul angle

/-- Reversing the rotation angle exchanges the diagonal spinor and its inverse. -/
private theorem inPlaneSpinRotation_neg (angle : ℝ) :
    inPlaneSpinRotation (-angle) = inPlaneSpinRotationInverse angle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sub_eq_add_neg]

private theorem inPlaneSpinRotationInverse_neg (angle : ℝ) :
    inPlaneSpinRotationInverse (-angle) = inPlaneSpinRotation angle := by
  simpa only [neg_neg] using (inPlaneSpinRotation_neg (-angle)).symm

/-- The inverse spinor can also be placed on the left. -/
theorem inPlaneSpinRotationInverse_mul (angle : ℝ) :
    inPlaneSpinRotationInverse angle * inPlaneSpinRotation angle = 1 := by
  simpa only [inPlaneSpinRotation_neg, inPlaneSpinRotationInverse_neg] using
    inPlaneSpinRotation_mul_inverse (-angle)

/-- Entrywise conjugation by the diagonal in-plane spinor multiplies each
matrix entry by the corresponding left and right spinor phases.
This avoids expanding a full matrix product in Fourier-kernel proofs. -/
theorem inPlaneSpinRotation_conjugate_apply
    (angle : ℝ) (M : PauliMatrix) (i j : Fin 2) :
    (inPlaneSpinRotation angle * M * inPlaneSpinRotationInverse angle) i j =
      inPlaneSpinRotation angle i i * M i j *
        inPlaneSpinRotationInverse angle j j := by
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two, mul_assoc]

/-- Conjugation by the diagonal spinor fixes every diagonal entry. -/
theorem inPlaneSpinRotation_conjugate_diagonal
    (angle : ℝ) (M : PauliMatrix) (i : Fin 2) :
    (inPlaneSpinRotation angle * M * inPlaneSpinRotationInverse angle) i i = M i i := by
  rw [inPlaneSpinRotation_conjugate_apply]
  fin_cases i
  · simp [inPlaneSpinRotation, inPlaneSpinRotationInverse]
  · change
      ((((Real.cos angle : ℝ) : ℂ) + Complex.I * ((Real.sin angle : ℝ) : ℂ))) *
          M 1 1 *
          ((((Real.cos angle : ℝ) : ℂ) - Complex.I * ((Real.sin angle : ℝ) : ℂ))) =
        M 1 1
    rw [mul_right_comm, inPlaneSpinRotation_phases_mul, one_mul]

/-- Rotating the Pauli-x axis produces the polar in-plane Pauli direction. -/
theorem inPlaneSpinRotation_pauliX (angle : ℝ) :
    inPlaneSpinRotation angle * pauliX * inPlaneSpinRotationInverse angle =
      (((Real.cos angle : ℝ) : ℂ)) • pauliX +
        (((Real.sin angle : ℝ) : ℂ)) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, pauliX, pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul]
  all_goals ring_nf

/-- Rotating the Pauli-y axis gives its oriented orthogonal partner. -/
theorem inPlaneSpinRotation_pauliY (angle : ℝ) :
    inPlaneSpinRotation angle * pauliY * inPlaneSpinRotationInverse angle =
      -(((Real.sin angle : ℝ) : ℂ)) • pauliX +
        (((Real.cos angle : ℝ) : ℂ)) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, pauliX, pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul]
  all_goals ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- The third Pauli axis is invariant under in-plane spinor rotation. -/
theorem inPlaneSpinRotation_pauliZ (angle : ℝ) :
    inPlaneSpinRotation angle * pauliZ * inPlaneSpinRotationInverse angle = pauliZ := by
  have hcomm :
      inPlaneSpinRotation angle * pauliZ = pauliZ * inPlaneSpinRotation angle := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [inPlaneSpinRotation, pauliZ,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [hcomm, mul_assoc, inPlaneSpinRotation_mul_inverse, mul_one]

/-- Inverse rotation on the semantic Pauli axes, including the invariant z axis. -/
theorem inPlaneSpinRotationInverse_pauliBasis (axis : PauliAxis) (angle : ℝ) :
    inPlaneSpinRotationInverse angle * pauliBasis axis * inPlaneSpinRotation angle =
      pauliAxisComponent axis
        ((((Real.cos angle : ℝ) : ℂ)) • pauliX -
          (((Real.sin angle : ℝ) : ℂ)) • pauliY)
        ((((Real.sin angle : ℝ) : ℂ)) • pauliX +
          (((Real.cos angle : ℝ) : ℂ)) • pauliY)
        pauliZ := by
  cases axis
  · simpa [pauliBasis, pauliAxisComponent, inPlaneSpinRotation_neg,
      inPlaneSpinRotationInverse_neg, Real.cos_neg, Real.sin_neg, sub_eq_add_neg] using
      (inPlaneSpinRotation_pauliX (-angle))
  · simpa [pauliBasis, pauliAxisComponent, inPlaneSpinRotation_neg,
      inPlaneSpinRotationInverse_neg, Real.cos_neg, Real.sin_neg] using
      (inPlaneSpinRotation_pauliY (-angle))
  · simpa [pauliBasis, pauliAxisComponent, inPlaneSpinRotation_neg,
      inPlaneSpinRotationInverse_neg] using inPlaneSpinRotation_pauliZ (-angle)

/-- Polar Pauli matrix with a single radial in-plane coefficient. -/
def polarPauliMatrix (a b d : ℂ) (θ : ℝ) : PauliMatrix :=
  a • (1 : PauliMatrix) +
    (((Real.cos θ : ℝ) : ℂ) * b) • pauliX +
    (((Real.sin θ : ℝ) : ℂ) * b) • pauliY +
    d • pauliZ

/-- Polar Pauli matrices are conjugate to their radial-axis specialization
under the in-plane spinor rotation. -/
theorem polarPauliMatrix_eq_spinRotation (a b d : ℂ) (angle : ℝ) :
    polarPauliMatrix a b d angle =
      inPlaneSpinRotation angle * polarPauliMatrix a b d 0 *
        inPlaneSpinRotationInverse angle := by
  have hP0 :
      polarPauliMatrix a b d 0 =
        a • (1 : PauliMatrix) + b • pauliX + d • pauliZ := by
    simp [polarPauliMatrix]
  rw [hP0]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_one, inPlaneSpinRotation_mul_inverse, inPlaneSpinRotation_pauliX,
    inPlaneSpinRotation_pauliZ]
  unfold polarPauliMatrix
  module

/-- A matrix sandwiched between two polar Pauli matrices transports to the radial axis
by inverse spinor conjugation of the middle matrix. -/
theorem polarPauliMatrix_sandwich_spinRotation
    (aA bA dA aR bR dR : ℂ) (vertex : PauliMatrix) (angle : ℝ) :
    polarPauliMatrix aA bA dA angle * vertex *
        polarPauliMatrix aR bR dR angle =
      inPlaneSpinRotation angle *
        (polarPauliMatrix aA bA dA 0 *
          (inPlaneSpinRotationInverse angle * vertex *
            inPlaneSpinRotation angle) *
          polarPauliMatrix aR bR dR 0) *
        inPlaneSpinRotationInverse angle := by
  rw [polarPauliMatrix_eq_spinRotation aA bA dA angle,
    polarPauliMatrix_eq_spinRotation aR bR dR angle]
  simp only [Matrix.mul_assoc]


end

end InternalSpace
