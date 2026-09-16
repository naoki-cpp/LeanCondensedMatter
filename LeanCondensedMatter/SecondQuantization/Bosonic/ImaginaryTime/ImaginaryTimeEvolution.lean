import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.CreationAnnihilation
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.EnergyShift
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Bosonic imaginary-time theory

This module contains the bosonic imaginary-time layer:

- the free-energy eigenvalue and diagonal free Hamiltonian;
- algebraic free and Heisenberg imaginary-time evolution;
- fixed energy shifts and evolved creation/annihilation operators;
- the algebraic interaction-picture operator.

All constructions are algebraic. No operator exponential, Hilbert-space completion, positivity
assumption on the dispersion, or convergence theorem is used.

Generic semigroup, inverse, zero-time, and composition laws for diagonal/Heisenberg evolution are
owned by `SecondQuantization.Common.ImaginaryTime.DiagonalEvolution`. Fixed energy-shift
eigenoperator laws are owned by `SecondQuantization.Common.ImaginaryTime.EnergyShift`. Generic
interaction-picture matrix-coefficient, continuity, and interval-integrability facts are owned by
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
  Common.diagonalOperator fun n : Occupation Mode => (freeEigenvalue ε n : ℂ)

theorem freeHamiltonian_basisState (ε : Mode → ℝ) (n : Occupation Mode) :
    freeHamiltonian ε (basisState n) = (freeEigenvalue ε n : ℂ) • basisState n :=
  Common.diagonalOperator_basisState _ n

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
  simpa only [imaginaryTimeEvolve, freeHamiltonian] using
    Common.heisenbergEvolve_diagonalOperator (freeEigenvalue ε) τ
      (fun n : Occupation Mode => (freeEigenvalue ε n : ℂ))

/-! ## Energy shifts of creation and annihilation -/

/-- Annihilation at mode `i` carries free-energy shift `-ε i`. -/
theorem carriesEnergyShift_annihilate (ε : Mode → ℝ) (i : Mode) :
    Common.CarriesShift (freeEigenvalue ε) (annihilate i) (-ε i) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : n i = 0
  · exfalso
    apply hmn
    rw [annihilate_basisState_of_zero hi]
    rfl
  · have hm : m = removeOccupation i n := by
      by_contra hne
      apply hmn
      rw [annihilate_basisState_of_pos hi]
      exact Common.smul_basisState_apply_of_ne _ (Ne.symm hne)
    subst m
    rw [freeEigenvalue_removeOccupation_of_pos hi]
    ring

/-- Creation at mode `i` carries free-energy shift `+ε i`. -/
theorem carriesEnergyShift_create (ε : Mode → ℝ) (i : Mode) :
    Common.CarriesShift (freeEigenvalue ε) (create i) (ε i) := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  have hm : m = createOccupation i n := by
    by_contra hne
    apply hmn
    rw [create_basisState_eq]
    exact Common.smul_basisState_apply_of_ne _ (Ne.symm hne)
  subst m
  rw [freeEigenvalue_createOccupation]

/-- The annihilation operator evolves with energy shift `-ε i`. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  change Common.heisenbergEvolve (freeEigenvalue ε) τ (annihilate i) = _
  simpa [mul_neg, neg_mul] using
    Common.heisenbergEvolve_eq_smul_of_carriesShift
      (freeEigenvalue ε) (-ε i) τ (annihilate i) (carriesEnergyShift_annihilate ε i)

/-- The creation operator evolves with energy shift `ε i`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  change Common.heisenbergEvolve (freeEigenvalue ε) τ (create i) = _
  simpa using
    Common.heisenbergEvolve_eq_smul_of_carriesShift
      (freeEigenvalue ε) (ε i) τ (create i) (carriesEnergyShift_create ε i)

/-- Move an annihilation operator through the free diagonal evolution. -/
theorem imaginaryTimeEvolveFree_comp_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) •
        ((annihilate i).comp (imaginaryTimeEvolveFree ε τ)) := by
  change (Common.diagonalEvolution (freeEigenvalue ε) τ).comp (annihilate i) = _
  simpa [imaginaryTimeEvolveFree, mul_neg, neg_mul] using
    Common.diagonalEvolution_comp_of_carriesShift
      (freeEigenvalue ε) (-ε i) τ (annihilate i) (carriesEnergyShift_annihilate ε i)

/-- Move a creation operator through the free diagonal evolution. -/
theorem imaginaryTimeEvolveFree_comp_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) •
        ((create i).comp (imaginaryTimeEvolveFree ε τ)) := by
  change (Common.diagonalEvolution (freeEigenvalue ε) τ).comp (create i) = _
  simpa [imaginaryTimeEvolveFree] using
    Common.diagonalEvolution_comp_of_carriesShift
      (freeEigenvalue ε) (ε i) τ (create i) (carriesEnergyShift_create ε i)

/-- The interaction-picture operator `V_I(τ) = e^{τH₀} V e^{-τH₀}`. -/
noncomputable def interactionPicture (ε : Mode → ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (τ : ℝ) :
    FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.interactionPicture (freeEigenvalue ε) V τ

end

end Bosonic
end SecondQuantization
