import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Imaginary-time evolution under the free bosonic Hamiltonian

Phase B2 of Track D's bosonic line (`notes/roadmaps/second-quantization.md`), mirroring
`Fermionic/ImaginaryTimeEvolution.lean` one step behind: `e^{τH₀}` for the free bosonic
Hamiltonian (diagonal in the occupation-number basis, eigenvalue `E(n) := Σᵢ n(i)·ε(i)`), the
Heisenberg-picture evolution `A(τ) := e^{τH₀} A e^{-τH₀}` of a general operator, and the evolved
creation/annihilation operators `a_i(τ) = e^{-τε_i} a_i`, `a_i†(τ) = e^{τε_i} a_i†`.

Unlike the fermionic case, there is no separate `Hamiltonian.lean` yet — `freeEigenvalue` here
plays that role for the diagonal free Hamiltonian only, exactly as `imaginaryTimeEvolveFreeBasis`
in the fermionic file uses `∑ i ∈ n, ε i` directly without a prior `freeHamiltonian` definition.
The occupation sum `freeEigenvalue` is additive under `createOccupation`/`removeOccupation`
(`freeEigenvalue_createOccupation`/`_removeOccupation_of_pos`), proved via the additivity of
`Finsupp.sum` rather than the fermionic file's `Finset.sum_insert`/`add_sum_erase` — the bosonic
occupation-number sum has no membership case to split on, only a value that may be zero.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-! ## The free-Hamiltonian eigenvalue `E(n) := Σᵢ n(i)·ε(i)` -/

/-- **The free-Hamiltonian eigenvalue** of an occupation state, `E(n) := Σᵢ n(i)·ε(i)`. -/
def freeEigenvalue (ε : Mode → ℝ) (n : Occupation Mode) : ℂ :=
  n.sum fun i k => (k : ℂ) * (ε i : ℂ)

omit [DecidableEq Mode] in
theorem freeEigenvalue_add (ε : Mode → ℝ) (m n : Occupation Mode) :
    freeEigenvalue ε (m + n) = freeEigenvalue ε m + freeEigenvalue ε n :=
  Finsupp.sum_add_index' (fun i => by simp) (fun i k1 k2 => by push_cast; ring)

omit [DecidableEq Mode] in
theorem freeEigenvalue_singleOccupation (ε : Mode → ℝ) (i : Mode) :
    freeEigenvalue ε (singleOccupation i) = (ε i : ℂ) := by
  simp [freeEigenvalue, singleOccupation]

omit [DecidableEq Mode] in
theorem freeEigenvalue_createOccupation (ε : Mode → ℝ) (i : Mode) (n : Occupation Mode) :
    freeEigenvalue ε (createOccupation i n) = freeEigenvalue ε n + (ε i : ℂ) := by
  rw [createOccupation, freeEigenvalue_add, freeEigenvalue_singleOccupation]

omit [DecidableEq Mode] in
theorem freeEigenvalue_removeOccupation_of_pos {ε : Mode → ℝ} {i : Mode} {n : Occupation Mode}
    (h : n i ≠ 0) :
    freeEigenvalue ε (removeOccupation i n) = freeEigenvalue ε n - (ε i : ℂ) := by
  have heq := freeEigenvalue_createOccupation ε i (removeOccupation i n)
  rw [createOccupation_removeOccupation_of_pos h] at heq
  linear_combination -heq

/-! ## `e^{τH₀}` for the free bosonic Hamiltonian -/

/-- **`e^{τH₀}`, on a basis state.** `Complex.exp (τ * E(n)) • basisState n`. -/
noncomputable def imaginaryTimeEvolveFreeBasis (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    FockSpaceBosonic Mode :=
  Complex.exp ((τ : ℂ) * freeEigenvalue ε n) • basisState n

/-- **The imaginary-time evolution operator `e^{τH₀}` for the free Hamiltonian**, extended
linearly from `imaginaryTimeEvolveFreeBasis`. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Finsupp.lift (FockSpaceBosonic Mode) ℂ (Occupation Mode) (imaginaryTimeEvolveFreeBasis ε τ)

theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp ((τ : ℂ) * freeEigenvalue ε n) • basisState n := by
  change Finsupp.lift _ ℂ _ (imaginaryTimeEvolveFreeBasis ε τ) (Finsupp.single n 1) =
    imaginaryTimeEvolveFreeBasis ε τ n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index, imaginaryTimeEvolveFreeBasis]

/-- **`e^{0·H₀} = id`.** -/
@[simp]
theorem imaginaryTimeEvolveFree_zero (ε : Mode → ℝ) :
    imaginaryTimeEvolveFree ε 0 = LinearMap.id := by
  apply linearMap_ext_basisState
  intro n
  simp [imaginaryTimeEvolveFree_basisState]

/-- **The one-parameter semigroup law**, `e^{τH₀} ∘ e^{τ'H₀} = e^{(τ+τ')H₀}`, proved directly from
`Complex.exp`'s additive law on the shared eigenbasis. -/
theorem imaginaryTimeEvolveFree_add (ε : Mode → ℝ) (τ τ' : ℝ) :
    (imaginaryTimeEvolveFree ε τ).comp (imaginaryTimeEvolveFree ε τ') =
      imaginaryTimeEvolveFree ε (τ + τ') := by
  apply linearMap_ext_basisState
  intro n
  rw [LinearMap.comp_apply, imaginaryTimeEvolveFree_basisState, map_smul,
    imaginaryTimeEvolveFree_basisState, imaginaryTimeEvolveFree_basisState, smul_smul,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **`e^{τH₀}` and `e^{-τH₀}` are mutually inverse.** -/
@[simp]
theorem imaginaryTimeEvolveFree_comp_neg (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε τ).comp (imaginaryTimeEvolveFree ε (-τ)) = LinearMap.id := by
  rw [imaginaryTimeEvolveFree_add]
  simp

@[simp]
theorem imaginaryTimeEvolveFree_neg_comp (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε (-τ)).comp (imaginaryTimeEvolveFree ε τ) = LinearMap.id := by
  rw [imaginaryTimeEvolveFree_add]
  simp

/-! ## The Heisenberg-picture evolution of a general operator -/

/-- **The imaginary-time (Heisenberg-picture) evolution of an operator `A` under the free
Hamiltonian**: `A(τ) := e^{τH₀} A e^{-τH₀}`. -/
noncomputable def imaginaryTimeEvolve (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  (imaginaryTimeEvolveFree ε τ).comp (A.comp (imaginaryTimeEvolveFree ε (-τ)))

/-- **At `τ = 0`, imaginary-time evolution is trivial**: `A(0) = A`. -/
@[simp]
theorem imaginaryTimeEvolve_zero (ε : Mode → ℝ)
    (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    imaginaryTimeEvolve ε 0 A = A := by
  simp [imaginaryTimeEvolve]

/-! ## Evolved creation and annihilation operators -/

/-- **The imaginary-time-evolved annihilation operator**: `a_i(τ) = e^{-τε_i} a_i`. The physical
content of the free-theory Heisenberg equation of motion `d/dτ a_i(τ) = [H₀, a_i(τ)] = -ε_i a_i(τ)`,
proved here directly from the basis-level action rather than by solving that ODE. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve, LinearMap.comp_apply, LinearMap.comp_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply]
  by_cases hi : n i = 0
  · rw [annihilate_basisState_of_zero hi, smul_zero, map_zero, smul_zero]
  · have hexp : (-τ : ℂ) * freeEigenvalue ε n +
        (τ : ℂ) * (freeEigenvalue ε n - (ε i : ℂ)) = -(τ : ℂ) * (ε i : ℂ) := by ring
    rw [annihilate_basisState_of_pos hi, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
      smul_smul, freeEigenvalue_removeOccupation_of_pos hi, mul_right_comm, ← Complex.exp_add,
      Complex.ofReal_neg, hexp, smul_smul]

/-- **The imaginary-time-evolved creation operator**: `a_i†(τ) = e^{τε_i} a_i†`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) = Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  apply linearMap_ext_basisState
  intro n
  have hexp : (-τ : ℂ) * freeEigenvalue ε n +
      (τ : ℂ) * (freeEigenvalue ε n + (ε i : ℂ)) = (τ : ℂ) * (ε i : ℂ) := by ring
  rw [imaginaryTimeEvolve, LinearMap.comp_apply, LinearMap.comp_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply, create_basisState_eq,
    smul_smul, map_smul, imaginaryTimeEvolveFree_basisState, smul_smul,
    freeEigenvalue_createOccupation, mul_right_comm, ← Complex.exp_add, Complex.ofReal_neg, hexp,
    smul_smul]

end Bosonic
end SecondQuantization
