import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.EnergyShift
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Imaginary-time evolution under the free Hamiltonian

Beginning of the finite-temperature Green-function / time-ordered-correlator line: the genuine
Linked Cluster Theorem needs free imaginary-time evolution, time ordering, and thermal `n`-point
correlators — none of which `FormalLogPartitionFunction.lean`'s purely combinatorial `log Z`
groundwork provides on its own. This file is step 1: an algebraic, basis-diagonal realization of
free evolution for `H₀ = freeHamiltonian ε` only.

This file defines the scalar action of free evolution directly on each basis vector:
`Complex.exp (τ * E(n)) • |n⟩`, where `E(n) := fermionEnergy ε n`. This is an algebraic,
basis-diagonal realization, not an analytic operator exponential: `FockSpace Mode` has
no topology or Hilbert completion in this development. The construction does not require an
operator-norm limit, but that is because no operator exponential is being constructed here. This
diagonal definition is specific to a *diagonal* Hamiltonian; it does not extend to a general
`H = H₀ + V` (that is exactly why the interaction picture and Dyson series are needed for anything
beyond the free theory).

Generic semigroup, inverse, zero-time laws for the diagonal and Heisenberg evolutions are owned
by `SecondQuantization.Common.ImaginaryTime.DiagonalEvolution`. Fixed energy-shift eigenoperator
laws are owned by `SecondQuantization.Common.ImaginaryTime.EnergyShift`.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- **The imaginary-time evolution operator `e^{τH₀}` for the free Hamiltonian**: the algebraic,
basis-diagonal realization from `Common.diagonalEvolution`, specialized to `fermionEnergy`. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.diagonalEvolution (fermionEnergy ε) τ

omit [LinearOrder Mode] in
theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp ((τ * fermionEnergy ε n : ℝ) : ℂ) • basisState n := by
  simp only [imaginaryTimeEvolveFree, basisState]
  exact Common.diagonalEvolution_basisState (fermionEnergy ε) τ n

/-! ## Algebraic Heisenberg-type evolution of a general operator -/

/-- **The algebraic imaginary-time conjugation of an operator `A` under the free diagonal
evolution**: notation `A(τ) := e^{τH₀} A e^{-τH₀}` for the two basis-diagonal realizations above.
It is well-defined for *any* algebraic linear map `A`, but this file does not construct analytic
operators or a completed Hilbert-space conjugation. -/
noncomputable def imaginaryTimeEvolve (ε : Mode → ℝ) (τ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.heisenbergEvolve (fermionEnergy ε) τ A

omit [LinearOrder Mode] in
/-- Unfolds `imaginaryTimeEvolve` back down to `imaginaryTimeEvolveFree`, matching the shape most
proofs below need — `A(τ) := e^{τH₀} A e^{-τH₀}`, applied to a vector. -/
theorem imaginaryTimeEvolve_apply (ε : Mode → ℝ) (τ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (x : OccupationFock Mode) :
    imaginaryTimeEvolve ε τ A x =
      imaginaryTimeEvolveFree ε τ (A (imaginaryTimeEvolveFree ε (-τ) x)) :=
  rfl

omit [LinearOrder Mode] in
/-- **The free Hamiltonian evolves trivially under its own flow**: `H₀(τ) = H₀`, since `H₀` is
diagonal in the very basis `e^{τH₀}` acts on by a scalar. -/
theorem imaginaryTimeEvolve_freeHamiltonian (ε : Mode → ℝ) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (freeHamiltonian ε) = freeHamiltonian ε := by
  simpa only [imaginaryTimeEvolve, freeHamiltonian] using
    Common.heisenbergEvolve_diagonalOperator (fermionEnergy ε) τ
      (fun n : Occupation Mode => (fermionEnergy ε n : ℂ))

/-! ## Energy shifts of creation and annihilation -/

/-- Annihilation at mode `i` carries free-energy shift `-ε i`. -/
theorem carriesEnergyShift_annihilate (ε : Mode → ℝ) (i : Mode) :
    Common.CarriesShift (fermionEnergy ε) (annihilate i) (-ε i) := by
  intro m n hmn
  change annihilate i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · have hm : m = removeOccupation i n := by
      by_contra hne
      apply hmn
      rw [annihilate_basisState_of_mem hi]
      exact Common.smul_basisState_apply_of_ne _ (Ne.symm hne)
    subst m
    rw [fermionEnergy_removeOccupation_of_mem hi]
    ring
  · exfalso
    apply hmn
    rw [annihilate_basisState_of_not_mem hi]
    rfl

/-- Creation at mode `i` carries free-energy shift `+ε i`. -/
theorem carriesEnergyShift_create (ε : Mode → ℝ) (i : Mode) :
    Common.CarriesShift (fermionEnergy ε) (create i) (ε i) := by
  intro m n hmn
  change create i (basisState n) m ≠ 0 at hmn
  by_cases hi : i ∈ n
  · exfalso
    apply hmn
    rw [create_basisState_of_mem hi]
    rfl
  · have hm : m = insertOccupation i n := by
      by_contra hne
      apply hmn
      rw [create_basisState_of_not_mem hi]
      exact Common.smul_basisState_apply_of_ne _ (Ne.symm hne)
    subst m
    rw [fermionEnergy_insertOccupation_of_not_mem hi]

/-! ## Evolved creation and annihilation operators -/

/-- **The imaginary-time-evolved annihilation operator**: `c_i(τ) = e^{-τε_i} c_i`. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) = Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  change Common.heisenbergEvolve (fermionEnergy ε) τ (annihilate i) = _
  simpa [mul_neg, neg_mul] using
    Common.heisenbergEvolve_eq_smul_of_carriesShift
      (fermionEnergy ε) (-ε i) τ (annihilate i) (carriesEnergyShift_annihilate ε i)

/-- **The imaginary-time-evolved creation operator**: `c_i†(τ) = e^{τε_i} c_i†`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) = Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  change Common.heisenbergEvolve (fermionEnergy ε) τ (create i) = _
  simpa using
    Common.heisenbergEvolve_eq_smul_of_carriesShift
      (fermionEnergy ε) (ε i) τ (create i) (carriesEnergyShift_create ε i)

/-! ## The KMS-type commutation relation with `e^{τH₀}` -/

/-- **The KMS-type relation for the annihilation operator**: `e^{τH₀} c_i = e^{-τε_i} c_i e^{τH₀}`. -/
theorem imaginaryTimeEvolveFree_comp_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • ((annihilate i).comp (imaginaryTimeEvolveFree ε τ)) := by
  change (Common.diagonalEvolution (fermionEnergy ε) τ).comp (annihilate i) = _
  simpa [imaginaryTimeEvolveFree, mul_neg, neg_mul] using
    Common.diagonalEvolution_comp_of_carriesShift
      (fermionEnergy ε) (-ε i) τ (annihilate i) (carriesEnergyShift_annihilate ε i)

/-- **The KMS-type relation for the creation operator**: `e^{τH₀} c_i† = e^{τε_i} c_i† e^{τH₀}`. -/
theorem imaginaryTimeEvolveFree_comp_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • ((create i).comp (imaginaryTimeEvolveFree ε τ)) := by
  change (Common.diagonalEvolution (fermionEnergy ε) τ).comp (create i) = _
  simpa [imaginaryTimeEvolveFree] using
    Common.diagonalEvolution_comp_of_carriesShift
      (fermionEnergy ε) (ε i) τ (create i) (carriesEnergyShift_create ε i)

end Fermionic
end SecondQuantization
