import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Bosonic imaginary-time theory

This module contains the bosonic imaginary-time layer:

- the free-energy eigenvalue and diagonal free Hamiltonian;
- algebraic free and Heisenberg imaginary-time evolution;
- evolved creation and annihilation operators;
- the algebraic interaction-picture operator.

All constructions are algebraic. No operator exponential, Hilbert-space completion, positivity
assumption on the dispersion, or convergence theorem is used.

Generic semigroup, inverse, zero-time, and composition laws for diagonal/Heisenberg evolution are
owned by `SecondQuantization.Common.ImaginaryTime.DiagonalEvolution`. Generic interaction-picture
matrix-coefficient, continuity, and interval-integrability facts are owned by
`SecondQuantization.Common.ImaginaryTime.InteractionPicture`; Bosonic keeps only the physical
`freeEigenvalue` specialization and statistics-specific operator statements.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality, kept out of public theorem signatures. -/
local instance instDecidableEqImaginaryTimeEvolution : DecidableEq Mode := Classical.decEq Mode

/-- The free-Hamiltonian eigenvalue `E(n) = Σᵢ n(i) ε(i)`. -/
def freeEigenvalue (ε : Mode → ℝ) (n : Occupation Mode) : ℝ :=
  n.sum fun i k => (k : ℝ) * ε i

theorem freeEigenvalue_add (ε : Mode → ℝ) (m n : Occupation Mode) :
    freeEigenvalue ε (m + n) = freeEigenvalue ε m + freeEigenvalue ε n :=
  Finsupp.sum_add_index' (fun i => by simp) (fun i k1 k2 => by push_cast; ring)

theorem freeEigenvalue_singleOccupation (ε : Mode → ℝ) (i : Mode) :
    freeEigenvalue ε (singleOccupation i) = ε i := by
  simp [freeEigenvalue, singleOccupation]

theorem freeEigenvalue_createOccupation (ε : Mode → ℝ) (i : Mode) (n : Occupation Mode) :
    freeEigenvalue ε (createOccupation i n) = freeEigenvalue ε n + ε i := by
  rw [createOccupation, freeEigenvalue_add, freeEigenvalue_singleOccupation]

theorem freeEigenvalue_removeOccupation_of_pos {ε : Mode → ℝ} {i : Mode} {n : Occupation Mode}
    (h : n i ≠ 0) :
    freeEigenvalue ε (removeOccupation i n) = freeEigenvalue ε n - ε i := by
  have heq := freeEigenvalue_createOccupation ε i (removeOccupation i n)
  rw [createOccupation_removeOccupation_of_pos h] at heq
  linarith

/-- The free bosonic Hamiltonian, diagonal in the occupation basis. -/
noncomputable def freeHamiltonian (ε : Mode → ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Finsupp.lift (FockSpace Mode) ℂ (Occupation Mode)
    fun n => (freeEigenvalue ε n : ℂ) • basisState n

theorem freeHamiltonian_basisState (ε : Mode → ℝ) (n : Occupation Mode) :
    freeHamiltonian ε (basisState n) = (freeEigenvalue ε n : ℂ) • basisState n := by
  change Finsupp.lift _ ℂ _ (fun n => (freeEigenvalue ε n : ℂ) • basisState n)
    (Finsupp.single n 1) = (freeEigenvalue ε n : ℂ) • basisState n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- The diagonal algebraic realization of `e^{τH₀}`. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.diagonalEvolution (freeEigenvalue ε) τ

theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) • basisState n := by
  simp only [imaginaryTimeEvolveFree, basisState]
  exact Common.diagonalEvolution_basisState (freeEigenvalue ε) τ n

/-- Conjugation by the free diagonal evolution. -/
noncomputable def imaginaryTimeEvolve (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.heisenbergEvolve (freeEigenvalue ε) τ A

theorem imaginaryTimeEvolve_apply (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (x : FockSpace Mode) :
    imaginaryTimeEvolve ε τ A x =
      imaginaryTimeEvolveFree ε τ (A (imaginaryTimeEvolveFree ε (-τ) x)) :=
  rfl

/-- The free Hamiltonian is fixed by its own imaginary-time evolution. -/
theorem imaginaryTimeEvolve_freeHamiltonian (ε : Mode → ℝ) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (freeHamiltonian ε) = freeHamiltonian ε := by
  apply linearMap_ext_basisState
  intro n
  have hscalar : Complex.exp ((-τ * freeEigenvalue ε n : ℝ) : ℂ) *
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) = 1 := by
    rw [← Complex.exp_add, ← Complex.ofReal_add]
    norm_num
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, freeHamiltonian_basisState, smul_smul,
    map_smul, imaginaryTimeEvolveFree_basisState, smul_smul, mul_right_comm, hscalar, one_mul]

/-- The annihilation operator evolves with energy shift `-ε i`. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply]
  by_cases hi : n i = 0
  · rw [annihilate_basisState_of_zero hi, smul_zero, map_zero, smul_zero]
  · have hexp : -τ * freeEigenvalue ε n + τ * (freeEigenvalue ε n - ε i) = -τ * ε i := by
      ring
    have hcast : (-(τ : ℂ)) * (ε i : ℂ) = ((-τ * ε i : ℝ) : ℂ) := by
      push_cast
      ring
    rw [annihilate_basisState_of_pos hi, smul_smul, map_smul,
      imaginaryTimeEvolveFree_basisState, smul_smul, freeEigenvalue_removeOccupation_of_pos hi,
      mul_right_comm, hcast, ← Complex.exp_add, ← Complex.ofReal_add, hexp, smul_smul]

/-- The creation operator evolves with energy shift `ε i`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  apply linearMap_ext_basisState
  intro n
  have hexp : -τ * freeEigenvalue ε n + τ * (freeEigenvalue ε n + ε i) = τ * ε i := by
    ring
  have hcast : (τ : ℂ) * (ε i : ℂ) = ((τ * ε i : ℝ) : ℂ) := by
    push_cast
    ring
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply, create_basisState_eq,
    smul_smul, map_smul, imaginaryTimeEvolveFree_basisState, smul_smul,
    freeEigenvalue_createOccupation, mul_right_comm, hcast, ← Complex.exp_add,
    ← Complex.ofReal_add, hexp, smul_smul]

/-- Move an annihilation operator through the free diagonal evolution. -/
theorem imaginaryTimeEvolveFree_comp_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) •
        ((annihilate i).comp (imaginaryTimeEvolveFree ε τ)) := by
  have hcast : ((-ε i * τ : ℝ) : ℂ) = -(τ : ℂ) * (ε i : ℂ) := by
    push_cast
    ring
  have h := Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
    (freeEigenvalue ε) τ (-ε i) (annihilate i) (by
      rw [hcast]
      exact imaginaryTimeEvolve_annihilate ε τ i)
  rwa [hcast] at h

/-- Move a creation operator through the free diagonal evolution. -/
theorem imaginaryTimeEvolveFree_comp_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) •
        ((create i).comp (imaginaryTimeEvolveFree ε τ)) := by
  have hcast : ((ε i * τ : ℝ) : ℂ) = (τ : ℂ) * (ε i : ℂ) := by
    push_cast
    ring
  have h := Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
    (freeEigenvalue ε) τ (ε i) (create i) (by
      rw [hcast]
      exact imaginaryTimeEvolve_create ε τ i)
  rwa [hcast] at h

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.interactionPicture (freeEigenvalue ε) V τ

end

end Bosonic
end SecondQuantization
