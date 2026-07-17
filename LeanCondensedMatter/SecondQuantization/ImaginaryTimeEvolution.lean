import LeanCondensedMatter.SecondQuantization.HamiltonianFermionic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Imaginary-time evolution under the free Hamiltonian

Beginning of the finite-temperature Green-function / time-ordered-correlator line: the genuine
Linked Cluster Theorem needs actual imaginary-time evolution `A(τ) := e^{τH₀} A e^{-τH₀}`, time
ordering, and thermal `n`-point correlators — none of which `FormalLogPartitionFunction.lean`'s
purely combinatorial `log Z` groundwork provides on its own. This file is step 1: `e^{τH₀}` itself,
for the *free* Hamiltonian `H₀ = freeHamiltonian ε` only.

Unlike `FormalExpFermionic.lean`'s `formalExpTerm`/`formalExpTruncation` (a finite Taylor
truncation, since `FockSpaceFermionic Mode` has no topology for a genuine operator limit),
`e^{τH₀}` here is the **actual, non-truncated analytic exponential** — because `freeHamiltonian ε`
is diagonal in the occupation-number basis (`freeHamiltonian_basisState`) with eigenvalue
`E(n) := Σᵢ∈n ε(i) : ℝ`, so `e^{τH₀}` acts on each basis vector by the ordinary scalar
`Complex.exp (τ * E(n)) : ℂ` — no operator-norm limit is needed, only `Complex.exp` of a concrete
number. This trick is specific to a *diagonal* Hamiltonian; it does not extend to a general
`H = H₀ + V` (that is exactly why the interaction picture and Dyson series are needed for anything
beyond the free theory).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]

/-- **`e^{τH₀}`, on a basis state.** `Complex.exp (τ * E(n)) • basisState n`, where
`E(n) := Σᵢ∈n ε(i)` is the occupation state's free-Hamiltonian eigenvalue
(`freeHamiltonian_basisState`). -/
noncomputable def imaginaryTimeEvolveFreeBasis (ε : Mode → ℝ) (τ : ℝ)
    (n : FermionOccupation Mode) : FockSpaceFermionic Mode :=
  Complex.exp (τ * ∑ i ∈ n, (ε i : ℂ)) • basisState n

/-- **The imaginary-time evolution operator `e^{τH₀}` for the free Hamiltonian**, extended
linearly from `imaginaryTimeEvolveFreeBasis`. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Finsupp.lift (FockSpaceFermionic Mode) ℂ (FermionOccupation Mode)
    (imaginaryTimeEvolveFreeBasis ε τ)

omit [LinearOrder Mode] in
theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : FermionOccupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp (τ * ∑ i ∈ n, (ε i : ℂ)) • basisState n := by
  change Finsupp.lift _ ℂ _ (imaginaryTimeEvolveFreeBasis ε τ) (Finsupp.single n 1) =
    imaginaryTimeEvolveFreeBasis ε τ n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index, imaginaryTimeEvolveFreeBasis]

omit [LinearOrder Mode] in
/-- **`e^{0·H₀} = id`.** -/
@[simp]
theorem imaginaryTimeEvolveFree_zero (ε : Mode → ℝ) :
    imaginaryTimeEvolveFree ε 0 = LinearMap.id := by
  apply linearMap_ext_basisState
  intro n
  simp [imaginaryTimeEvolveFree_basisState]

omit [LinearOrder Mode] in
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

omit [LinearOrder Mode] in
/-- **`e^{τH₀}` and `e^{-τH₀}` are mutually inverse.** -/
@[simp]
theorem imaginaryTimeEvolveFree_comp_neg (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε τ).comp (imaginaryTimeEvolveFree ε (-τ)) = LinearMap.id := by
  rw [imaginaryTimeEvolveFree_add]
  simp

omit [LinearOrder Mode] in
@[simp]
theorem imaginaryTimeEvolveFree_neg_comp (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε (-τ)).comp (imaginaryTimeEvolveFree ε τ) = LinearMap.id := by
  rw [imaginaryTimeEvolveFree_add]
  simp

/-! ## The Heisenberg-picture evolution of a general operator -/

/-- **The imaginary-time (Heisenberg-picture) evolution of an operator `A` under the free
Hamiltonian**: `A(τ) := e^{τH₀} A e^{-τH₀}`. Well-defined for *any* `A` (not just diagonal ones),
since `e^{±τH₀}` are the genuinely analytic, non-truncated operators above. -/
noncomputable def imaginaryTimeEvolve (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  (imaginaryTimeEvolveFree ε τ).comp (A.comp (imaginaryTimeEvolveFree ε (-τ)))

omit [LinearOrder Mode] in
/-- **At `τ = 0`, imaginary-time evolution is trivial**: `A(0) = A`. -/
@[simp]
theorem imaginaryTimeEvolve_zero (ε : Mode → ℝ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    imaginaryTimeEvolve ε 0 A = A := by
  simp [imaginaryTimeEvolve]

/-- **The free Hamiltonian evolves trivially under its own flow**: `H₀(τ) = H₀`, since `H₀` is
diagonal in the very basis `e^{τH₀}` acts on by a scalar. -/
theorem imaginaryTimeEvolve_freeHamiltonian [Fintype Mode] (ε : Mode → ℝ) (τ : ℝ) :
    imaginaryTimeEvolve ε τ (freeHamiltonian ε) = freeHamiltonian ε := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve, LinearMap.comp_apply, LinearMap.comp_apply,
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
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve, LinearMap.comp_apply, LinearMap.comp_apply,
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
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve, LinearMap.comp_apply, LinearMap.comp_apply,
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

end SecondQuantization
