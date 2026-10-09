import LeanCondensedMatter.SecondQuantization.Common.Algebra.SupportShift
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Parity conjugation on an algebraic Fock space

A parity-valued grading of the basis configurations defines a diagonal
involution. Conjugation by this involution acts by a fixed sign exactly
when an operator carries the corresponding support shift.

This is a basis-level operator statement. It does not impose graded
commutation relations between different operators or extend to completed
Hilbert-space operators.
-/

namespace SecondQuantization
namespace Common

/-- The complex character of the additive parity group `ZMod 2`. -/
def parityEigenvalue (p : ZMod 2) : ℂ :=
  if p = 0 then 1 else -1

@[simp]
theorem parityEigenvalue_zero : parityEigenvalue 0 = 1 := by
  simp [parityEigenvalue]

@[simp]
theorem parityEigenvalue_one : parityEigenvalue 1 = -1 := by
  norm_num [parityEigenvalue]

theorem parityEigenvalue_add (p q : ZMod 2) :
    parityEigenvalue (p + q) = parityEigenvalue p * parityEigenvalue q := by
  fin_cases p <;> fin_cases q <;> norm_num [parityEigenvalue]

theorem parityEigenvalue_sq (p : ZMod 2) :
    parityEigenvalue p * parityEigenvalue p = 1 := by
  fin_cases p <;> norm_num [parityEigenvalue]

/-- The character of a natural-number parity is the usual number-parity sign. -/
theorem parityEigenvalue_nat (n : ℕ) :
    parityEigenvalue (n : ZMod 2) = (-1 : ℂ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, parityEigenvalue_add, ih, parityEigenvalue_one, pow_succ]
      ring

private theorem parityEigenvalue_mul_iff (i j p : ZMod 2) :
    parityEigenvalue i * parityEigenvalue j = parityEigenvalue p ↔ i = j + p := by
  fin_cases i <;> fin_cases j <;> fin_cases p <;> norm_num [parityEigenvalue]

/-- The parity involution associated with a parity grading of basis configurations. -/
noncomputable def parityOperator {Config : Type*} (parity : Config → ZMod 2) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  diagonalOperator (fun n => parityEigenvalue (parity n))

@[simp]
theorem parityOperator_basisState {Config : Type*} (parity : Config → ZMod 2)
    (n : Config) :
    parityOperator parity (basisState n) =
      parityEigenvalue (parity n) • basisState n :=
  diagonalOperator_basisState _ n

theorem parityOperator_apply {Config : Type*} (parity : Config → ZMod 2)
    (x : AlgebraicFock Config) (n : Config) :
    parityOperator parity x n = parityEigenvalue (parity n) * x n :=
  diagonalOperator_apply _ x n

/-- Conjugating twice by parity is the identity. -/
theorem parityOperator_comp_self {Config : Type*} (parity : Config → ZMod 2) :
    (parityOperator parity).comp (parityOperator parity) =
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  apply linearMap_ext_basisState
  intro n
  simp only [LinearMap.comp_apply, parityOperator_basisState, map_smul,
    smul_smul, parityEigenvalue_sq, one_smul, LinearMap.id_apply]

private theorem matrixCoeff_parityOperator_conjugate {Config : Type*}
    (parity : Config → ZMod 2)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff ((parityOperator parity).comp (A.comp (parityOperator parity))) m n =
      (parityEigenvalue (parity m) * parityEigenvalue (parity n)) * matrixCoeff A m n := by
  change (parityOperator parity (A (parityOperator parity (basisState n)))) m = _
  rw [parityOperator_basisState, map_smul, parityOperator_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, matrixCoeff]
  ring

/-- A support shift of parity `p` is equivalent to conjugation by the
parity involution acting with eigenvalue `(-1)^p`. -/
theorem carriesShift_iff_parityOperator_conjugate {Config : Type*}
    (parity : Config → ZMod 2)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (p : ZMod 2) :
    CarriesShift parity A p ↔
      (parityOperator parity).comp (A.comp (parityOperator parity)) =
        parityEigenvalue p • A := by
  have hsmul (m n : Config) :
      matrixCoeff (parityEigenvalue p • A) m n =
        parityEigenvalue p * matrixCoeff A m n := by
    simpa only [matrixCoeffLinear_apply, smul_eq_mul] using
      (matrixCoeffLinear m n).map_smul (parityEigenvalue p) A
  constructor
  · intro hA
    apply matrixCoeff_ext
    intro m n
    rw [matrixCoeff_parityOperator_conjugate, hsmul]
    by_cases hmn : matrixCoeff A m n = 0
    · simp [hmn]
    · rw [(parityEigenvalue_mul_iff _ _ _).2 (hA m n hmn)]
  · intro hA
    intro m n hmn
    have h := congrArg (fun B => matrixCoeff B m n) hA
    rw [matrixCoeff_parityOperator_conjugate, hsmul] at h
    apply (parityEigenvalue_mul_iff _ _ _).1
    exact mul_right_cancel₀ hmn h

end Common
end SecondQuantization
