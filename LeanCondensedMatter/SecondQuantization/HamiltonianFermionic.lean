import LeanCondensedMatter.SecondQuantization.CanonicalAnticommutationRelations
import Mathlib.Algebra.Module.BigOperators

set_option linter.style.header false

/-!
# Fermionic number operator and Hamiltonians

Phase 6 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the
number operator `numberOperator i := create i ∘ annihilate i`, its eigenvalue equation on basis
states, and the free/interaction Hamiltonians built from it as finite sums of
creation/annihilation monomials — still on a finite mode set (`[Fintype Mode]`).

Field operators are still out of scope (see `CreationAnnihilationFermionic.lean`'s module
docstring); so is anything beyond the algebraic level (no self-adjointness, no spectral theory,
no completion) — those are deferred past the algebraic Linked Cluster Theorem, per this track's
design principles.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-! ## The number operator -/

/-- **The single-mode number operator** `Nᵢ := aᵢ† aᵢ`. -/
noncomputable def numberOperator (i : Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  (create i).comp (annihilate i)

theorem numberOperator_apply (i : Mode) (x : FockSpaceFermionic Mode) :
    numberOperator i x = create i (annihilate i x) :=
  rfl

/-- **The number-operator eigenvalue equation**, on basis states: `Nᵢ` acts as the identity on
occupied modes and as zero on unoccupied ones — occupation-number states are simultaneous
eigenvectors of every `numberOperator i`, with eigenvalue `0` or `1`. -/
theorem numberOperator_basisState (i : Mode) (n : FermionOccupation Mode) :
    numberOperator i (basisState n) = if i ∈ n then basisState n else 0 := by
  rw [numberOperator_apply]
  by_cases hi : i ∈ n
  · rw [if_pos hi]
    have hnotmem : i ∉ removeOccupation i n := Finset.notMem_erase i n
    have heq : insertOccupation i (removeOccupation i n) = n := by
      rw [insertOccupation, removeOccupation, Finset.insert_erase hi]
    rw [annihilate_basisState_of_mem hi, map_smul, create_basisState_of_not_mem hnotmem,
      fermionSign_removeOccupation_of_not_lt hi (lt_irrefl i), heq, smul_smul,
      fermionSign_sq_complex, one_smul]
  · rw [if_neg hi, annihilate_basisState_of_not_mem hi, map_zero]

/-! ## Free and interaction Hamiltonians -/

variable [Fintype Mode]

/-- **The total number operator**, `N := Σᵢ Nᵢ`. -/
noncomputable def totalNumberOperator : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ i : Mode, numberOperator i

theorem totalNumberOperator_basisState (n : FermionOccupation Mode) :
    totalNumberOperator (basisState n) = (fermionParticleNumber n : ℂ) • basisState n := by
  simp only [totalNumberOperator, LinearMap.sum_apply, numberOperator_basisState]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    show fermionParticleNumber n = n.card from rfl, ← Nat.cast_smul_eq_nsmul ℂ]

/-- **The free (non-interacting) Hamiltonian** for a dispersion `ε : Mode → ℝ`,
`H₀ := Σᵢ ε(i) Nᵢ`. -/
noncomputable def freeHamiltonian (ε : Mode → ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ i : Mode, (ε i : ℂ) • numberOperator i

theorem freeHamiltonian_basisState (ε : Mode → ℝ) (n : FermionOccupation Mode) :
    freeHamiltonian ε (basisState n) = (∑ i ∈ n, (ε i : ℂ)) • basisState n := by
  simp only [freeHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply,
    numberOperator_basisState, smul_ite, smul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_smul]

/-- **A density-density interaction Hamiltonian** for a coupling `V : Mode → Mode → ℝ`,
`H_int := Σᵢⱼ V(i,j) Nᵢ Nⱼ` — a concrete instance of "a finite sum of monomials in
creation/annihilation operators" (here, quartic monomials `aᵢ†aᵢaⱼ†aⱼ`). -/
noncomputable def interactionHamiltonian (V : Mode → Mode → ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  ∑ i : Mode, ∑ j : Mode, (V i j : ℂ) • ((numberOperator i).comp (numberOperator j))

theorem interactionHamiltonian_basisState (V : Mode → Mode → ℝ) (n : FermionOccupation Mode) :
    interactionHamiltonian V (basisState n) =
      (∑ i ∈ n, ∑ j ∈ n, (V i j : ℂ)) • basisState n := by
  simp only [interactionHamiltonian, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, numberOperator_basisState, apply_ite, map_zero, smul_zero]
  have hstep : ∀ x : Mode,
      (∑ y : Mode, if y ∈ n then (if x ∈ n then (V x y : ℂ) • basisState n else 0) else 0) =
        if x ∈ n then (∑ j ∈ n, (V x j : ℂ)) • basisState n else 0 := by
    intro x
    by_cases hx : x ∈ n
    · simp only [if_pos hx]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_smul]
    · simp [if_neg hx]
  simp_rw [hstep]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_smul]

end SecondQuantization
