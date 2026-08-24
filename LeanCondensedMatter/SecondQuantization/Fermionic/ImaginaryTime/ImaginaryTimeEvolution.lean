import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.DiagonalEvolution
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
`Complex.exp (τ * E(n)) • |n⟩`, where `E(n) := Σᵢ∈n ε(i) : ℝ`. This is an algebraic,
basis-diagonal realization, not an analytic operator exponential: `FockSpace Mode` has
no topology or Hilbert completion in this development. The construction does not require an
operator-norm limit, but that is because no operator exponential is being constructed here. This
diagonal definition is specific to a *diagonal* Hamiltonian; it does not extend to a general
`H = H₀ + V` (that is exactly why the interaction picture and Dyson series are needed for anything
beyond the free theory).

Generic semigroup, inverse, and zero-time laws for the diagonal and Heisenberg evolutions are owned
by `SecondQuantization.Common.ImaginaryTime.DiagonalEvolution` and consumed directly from there.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- **The free Hamiltonian's eigenvalue** on an occupation state, `E(n) := Σᵢ∈n ε(i) : ℝ`
(`freeHamiltonian_basisState`). Real-valued, matching `Common.DiagonalEvolution`'s `energy`
parameter — cast to `ℂ` only where `Complex.exp` needs it. -/
def fermionEnergy (ε : Mode → ℝ) (n : Occupation Mode) : ℝ := ∑ i ∈ n, ε i

omit [LinearOrder Mode] in
theorem fermionEnergy_eq_sum_complex (ε : Mode → ℝ) (n : Occupation Mode) :
    (fermionEnergy ε n : ℂ) = ∑ i ∈ n, (ε i : ℂ) := by
  simp [fermionEnergy]

/-- **The imaginary-time evolution operator `e^{τH₀}` for the free Hamiltonian**: the algebraic,
basis-diagonal realization from `Common.diagonalEvolution`, specialized to `fermionEnergy`. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.diagonalEvolution (fermionEnergy ε) τ

omit [LinearOrder Mode] in
theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp (τ * ∑ i ∈ n, (ε i : ℂ)) • basisState n := by
  simp only [imaginaryTimeEvolveFree, basisState]
  rw [Common.diagonalEvolution_basisState]
  congr 2
  push_cast [fermionEnergy]
  ring

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
  apply Common.linearMap_ext_basisState
  intro n
  change imaginaryTimeEvolve ε τ (freeHamiltonian ε) (basisState n) =
    freeHamiltonian ε (basisState n)
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, freeHamiltonian_basisState, smul_smul,
    map_smul, imaginaryTimeEvolveFree_basisState, smul_smul]
  congr 1
  have hx : (↑(-τ) : ℂ) * ∑ i ∈ n, (ε i : ℂ) = -((τ : ℂ) * ∑ i ∈ n, (ε i : ℂ)) := by
    push_cast; ring
  rw [hx, mul_right_comm, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-! ## Evolved creation and annihilation operators -/

/-- **The imaginary-time-evolved annihilation operator**: `c_i(τ) = e^{-τε_i} c_i`. The physical
content of the free-theory Heisenberg equation of motion `d/dτ c_i(τ) = [H₀, c_i(τ)] = -ε_i c_i(τ)`,
proved here directly from the basis-level action rather than by solving that ODE. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) = Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  apply Common.linearMap_ext_basisState
  intro n
  change imaginaryTimeEvolve ε τ (annihilate i) (basisState n) =
    (Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i) (basisState n)
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply]
  by_cases hi : i ∈ n
  · rw [annihilate_basisState_of_mem hi, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
      smul_smul, smul_smul]
    simp only [removeOccupation]
    push_cast
    have hsum : (ε i : ℂ) + ∑ x ∈ n.erase i, (ε x : ℂ) = ∑ x ∈ n, (ε x : ℂ) :=
      Finset.add_sum_erase n (fun x => (ε x : ℂ)) hi
    have hexp : -(τ : ℂ) * ∑ x ∈ n, (ε x : ℂ) + (τ : ℂ) * ∑ x ∈ n.erase i, (ε x : ℂ) =
        -(τ : ℂ) * (ε i : ℂ) := by
      linear_combination (τ : ℂ) * hsum
    rw [mul_right_comm, ← Complex.exp_add, hexp]
  · rw [annihilate_basisState_of_not_mem hi, smul_zero, map_zero, smul_zero]

/-- **The imaginary-time-evolved creation operator**: `c_i†(τ) = e^{τε_i} c_i†`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) = Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  apply Common.linearMap_ext_basisState
  intro n
  change imaginaryTimeEvolve ε τ (create i) (basisState n) =
    (Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i) (basisState n)
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply]
  by_cases hi : i ∈ n
  · rw [create_basisState_of_mem hi, smul_zero, map_zero, smul_zero]
  · rw [create_basisState_of_not_mem hi, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
      smul_smul, smul_smul]
    simp only [insertOccupation]
    push_cast
    have hsum : (ε i : ℂ) + ∑ x ∈ n, (ε x : ℂ) = ∑ x ∈ insert i n, (ε x : ℂ) := by
      rw [Finset.sum_insert hi]
    have hexp : -(τ : ℂ) * ∑ x ∈ n, (ε x : ℂ) + (τ : ℂ) * ∑ x ∈ insert i n, (ε x : ℂ) =
        (τ : ℂ) * (ε i : ℂ) := by
      linear_combination (-(τ : ℂ)) * hsum
    rw [mul_right_comm, ← Complex.exp_add, hexp]

/-! ## The KMS-type commutation relation with `e^{τH₀}` -/

/-- **The KMS-type relation for the annihilation operator**: `e^{τH₀} c_i = e^{-τε_i} c_i e^{τH₀}`
— an instance of `Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution`, from
`imaginaryTimeEvolve_annihilate`'s eigenvalue-shift `q := -ε_i`. Setting `τ := -β` and rearranging
gives the physics reference notes' `ĉ_i e^{-βĤ} = e^{-βε_i} e^{-βĤ} ĉ_i}`
(`quantum-statistical-mechanics.tex`'s "product-of-KMS-state-and-ladder-op"), the algebraic
ingredient the finite-temperature Bloch–de Dominicis theorem's induction needs to move a ladder
operator through the (would-be) Gibbs weight `e^{-βH₀}`. -/
theorem imaginaryTimeEvolveFree_comp_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • ((annihilate i).comp (imaginaryTimeEvolveFree ε τ)) := by
  have hcast : ((-ε i * τ : ℝ) : ℂ) = -(τ : ℂ) * (ε i : ℂ) := by push_cast; ring
  have h := Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
    (fermionEnergy ε) τ (-ε i) (annihilate i) (by
      rw [hcast]; exact imaginaryTimeEvolve_annihilate ε τ i)
  rwa [hcast] at h

/-- **The KMS-type relation for the creation operator**: `e^{τH₀} c_i† = e^{τε_i} c_i† e^{τH₀}`,
the creation-side mirror of `imaginaryTimeEvolveFree_comp_annihilate`. -/
theorem imaginaryTimeEvolveFree_comp_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    (imaginaryTimeEvolveFree ε τ).comp (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • ((create i).comp (imaginaryTimeEvolveFree ε τ)) := by
  have hcast : ((ε i * τ : ℝ) : ℂ) = (τ : ℂ) * (ε i : ℂ) := by push_cast; ring
  have h := Common.diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
    (fermionEnergy ε) τ (ε i) (create i) (by
      rw [hcast]; exact imaginaryTimeEvolve_create ε τ i)
  rwa [hcast] at h

end Fermionic
end SecondQuantization
