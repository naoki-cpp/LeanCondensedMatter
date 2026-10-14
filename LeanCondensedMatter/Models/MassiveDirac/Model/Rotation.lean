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
  fin_cases i <;> fin_cases j
  · simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [inPlaneSpinRotation, inPlaneSpinRotationInverse,
      Matrix.mul_apply, Fin.sum_univ_two] using
        inPlaneSpinRotation_phases_mul angle

/-- The inverse spinor can also be placed on the left. -/
theorem inPlaneSpinRotationInverse_mul (angle : ℝ) :
    inPlaneSpinRotationInverse angle * inPlaneSpinRotation angle = 1 := by
  calc
    inPlaneSpinRotationInverse angle * inPlaneSpinRotation angle =
        inPlaneSpinRotation angle * inPlaneSpinRotationInverse angle := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [inPlaneSpinRotation, inPlaneSpinRotationInverse,
          Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    _ = 1 := inPlaneSpinRotation_mul_inverse angle

/-- Entrywise conjugation by the diagonal in-plane spinor multiplies each
matrix entry by the corresponding left and right spinor phases.
This avoids expanding a full matrix product in Fourier-kernel proofs. -/
theorem inPlaneSpinRotation_conjugate_apply
    (angle : ℝ) (M : Matrix2) (i j : Fin 2) :
    (inPlaneSpinRotation angle * M * inPlaneSpinRotationInverse angle) i j =
      inPlaneSpinRotation angle i i * M i j *
        inPlaneSpinRotationInverse angle j j := by
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two, mul_assoc]

/-- Rotating the Pauli-x axis produces the polar in-plane Pauli direction. -/
theorem inPlaneSpinRotation_sigmaX (angle : ℝ) :
    inPlaneSpinRotation angle * sigmaX * inPlaneSpinRotationInverse angle =
      (((Real.cos angle : ℝ) : ℂ)) • sigmaX +
        (((Real.sin angle : ℝ) : ℂ)) • sigmaY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sigmaX, sigmaY,
      InternalSpace.pauliX, InternalSpace.pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul]
  all_goals ring_nf

/-- Rotating the Pauli-y axis gives its oriented orthogonal partner. -/
theorem inPlaneSpinRotation_sigmaY (angle : ℝ) :
    inPlaneSpinRotation angle * sigmaY * inPlaneSpinRotationInverse angle =
      -(((Real.sin angle : ℝ) : ℂ)) • sigmaX +
        (((Real.cos angle : ℝ) : ℂ)) • sigmaY := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sigmaX, sigmaY,
      InternalSpace.pauliX, InternalSpace.pauliY, Matrix.mul_apply,
      Fin.sum_univ_two, smul_eq_mul]
  all_goals ring_nf
  all_goals simp only [hI]
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
  rw [hcomm, mul_assoc, inPlaneSpinRotation_mul_inverse, mul_one]

/-- Reversing the rotation angle exchanges the diagonal spinor and its inverse. -/
private theorem inPlaneSpinRotation_neg (angle : ℝ) :
    inPlaneSpinRotation (-angle) = inPlaneSpinRotationInverse angle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sub_eq_add_neg]

private theorem inPlaneSpinRotationInverse_neg (angle : ℝ) :
    inPlaneSpinRotationInverse (-angle) = inPlaneSpinRotation angle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inPlaneSpinRotation, inPlaneSpinRotationInverse, sub_eq_add_neg]

/-- The inverse spinor rotates the Cartesian x-current vertex into the
cosine/sine combination needed for rotating a source-indexed current block. -/
theorem inPlaneSpinRotationInverse_sigmaX (angle : ℝ) :
    inPlaneSpinRotationInverse angle * sigmaX * inPlaneSpinRotation angle =
      (((Real.cos angle : ℝ) : ℂ)) • sigmaX -
        (((Real.sin angle : ℝ) : ℂ)) • sigmaY := by
  simpa [inPlaneSpinRotation_neg, inPlaneSpinRotationInverse_neg,
    Real.cos_neg, Real.sin_neg, sub_eq_add_neg] using
    (inPlaneSpinRotation_sigmaX (-angle))

/-- The inverse spinor rotates the Cartesian y-current vertex into the
orthogonal sine/cosine combination. -/
theorem inPlaneSpinRotationInverse_sigmaY (angle : ℝ) :
    inPlaneSpinRotationInverse angle * sigmaY * inPlaneSpinRotation angle =
      (((Real.sin angle : ℝ) : ℂ)) • sigmaX +
        (((Real.cos angle : ℝ) : ℂ)) • sigmaY := by
  simpa [inPlaneSpinRotation_neg, inPlaneSpinRotationInverse_neg,
    Real.cos_neg, Real.sin_neg] using
    (inPlaneSpinRotation_sigmaY (-angle))

/-- The physical source index picks the appropriate signed inverse spinor
rotation of the two Cartesian current vertices. The x and y source laws
remain in a single direction-indexed statement. -/
theorem inPlaneSpinRotationInverse_directionPauli (source : Fin 2) (angle : ℝ) :
    inPlaneSpinRotationInverse angle * directionPauli source *
        inPlaneSpinRotation angle =
      if source = 0 then
        (((Real.cos angle : ℝ) : ℂ)) • directionPauli 0 -
          (((Real.sin angle : ℝ) : ℂ)) • directionPauli 1
      else
        (((Real.sin angle : ℝ) : ℂ)) • directionPauli 0 +
          (((Real.cos angle : ℝ) : ℂ)) • directionPauli 1 := by
  fin_cases source
  · simpa [directionPauli, inPlanePauliAxis, InternalSpace.pauliBasis] using
      inPlaneSpinRotationInverse_sigmaX angle
  · simpa [directionPauli, inPlanePauliAxis, InternalSpace.pauliBasis] using
      inPlaneSpinRotationInverse_sigmaY angle

/-- Polar Pauli matrices are conjugate to their radial-axis specialization
under the physical in-plane spinor rotation. -/
theorem polarPauliMatrix_eq_spinRotation (a b d : ℂ) (angle : ℝ) :
    polarPauliMatrix a b d angle =
      inPlaneSpinRotation angle * polarPauliMatrix a b d 0 *
        inPlaneSpinRotationInverse angle := by
  have hP0 :
      polarPauliMatrix a b d 0 =
        a • (1 : Matrix2) + b • sigmaX + d • sigmaZ := by
    simp [polarPauliMatrix]
  rw [hP0]
  calc
    polarPauliMatrix a b d angle =
        a • (1 : Matrix2) +
          b • ((((Real.cos angle : ℝ) : ℂ)) • sigmaX +
            (((Real.sin angle : ℝ) : ℂ)) • sigmaY) +
          d • sigmaZ := by
            unfold polarPauliMatrix
            module
    _ = a • (inPlaneSpinRotation angle * (1 : Matrix2) *
              inPlaneSpinRotationInverse angle) +
          b • (inPlaneSpinRotation angle * sigmaX *
              inPlaneSpinRotationInverse angle) +
          d • (inPlaneSpinRotation angle * sigmaZ *
              inPlaneSpinRotationInverse angle) := by
            rw [inPlaneSpinRotation_sigmaX, inPlaneSpinRotation_sigmaZ]
            simp [inPlaneSpinRotation_mul_inverse]
    _ = inPlaneSpinRotation angle *
        (a • (1 : Matrix2) + b • sigmaX + d • sigmaZ) *
          inPlaneSpinRotationInverse angle := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/-- A current vertex sandwiched between two polar massive-Dirac matrices
transports to the radial axis by inverse spinor conjugation of that vertex.
This is the algebraic input for the source-indexed Gaussian crossed current
Fourier block; it makes no claim about integration or regulator limits. -/
theorem polarPauliMatrix_sandwich_spinRotation
    (aA bA dA aR bR dR : ℂ) (vertex : Matrix2) (angle : ℝ) :
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

end QuantumTheory.Models.MassiveDirac
