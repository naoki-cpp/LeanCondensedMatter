import LeanCondensedMatter.SecondQuantization.Bosonic.CCR
import LeanCondensedMatter.SecondQuantization.Common.DiagonalEvolution
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Imaginary-time evolution under the free bosonic Hamiltonian

Phase B2 of Track D's bosonic line (`notes/roadmaps/second-quantization.md`), mirroring
`Fermionic/ImaginaryTimeEvolution.lean` one step behind: the free bosonic Hamiltonian
`freeHamiltonian`, diagonal in the occupation-number basis with (real) eigenvalue
`E(n) := Σᵢ n(i)·ε(i)` (`freeEigenvalue`); the **algebraic, basis-diagonal realization** of
`e^{τH₀}` (`imaginaryTimeEvolveFree`) this diagonality gives directly, without constructing an
actual operator exponential or any topological completion of `FockSpaceBosonic Mode`; the
Heisenberg-picture evolution `A(τ) := e^{τH₀} A e^{-τH₀}` of a general operator; and the evolved
creation/annihilation operators `a_i(τ) = e^{-τε_i} a_i`, `a_i†(τ) = e^{τε_i} a_i†`.

`imaginaryTimeEvolveFree ε τ` sends `|n⟩ ↦ exp(τ E(n)) • |n⟩` directly from `E(n)`'s value — this
is the diagonal *definition* of `e^{τH₀}` on this eigenbasis, not a derived fact about applying
`Complex.exp` to `freeHamiltonian` as an operator (no operator-valued exponential is constructed
anywhere in this file). `freeHamiltonian_basisState` below records how the two relate:
`freeHamiltonian` and `imaginaryTimeEvolveFree` share the same eigenbasis and eigenvalue `E(n)`,
by definition of both.

`ε : Mode → ℝ` carries no positivity or boundedness assumption in this file — none of the
algebraic identities here need one. Phase B3's planned finite-occupation-cutoff thermal trace
needs no convergence theorem either, since a cutoff sum is finite regardless of `ε`'s sign.
Positivity/convergence conditions on `ε` (e.g. `βεᵢ > 0` per mode) only become necessary once the
cutoff is later removed for a genuine, uncutoff bosonic thermal partition function — a further
step past B3, not B3 itself.

`freeEigenvalue` is additive under `createOccupation`/`removeOccupation`
(`freeEigenvalue_createOccupation`/`_removeOccupation_of_pos`), proved via the additivity of
`Finsupp.sum` rather than the fermionic file's `Finset.sum_insert`/`add_sum_erase` — the bosonic
occupation-number sum has no membership case to split on, only a value that may be zero.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-! ## The free-Hamiltonian eigenvalue `E(n) := Σᵢ n(i)·ε(i)` -/

/-- **The free-Hamiltonian eigenvalue** of an occupation state, `E(n) := Σᵢ n(i)·ε(i)`. Real —
`ε` is a real dispersion, and each occupation number is a natural number — matching the physical
reading as an energy; only cast to `ℂ` where `Complex.exp` needs it (`imaginaryTimeEvolveFreeBasis`,
`freeHamiltonian`). -/
def freeEigenvalue (ε : Mode → ℝ) (n : Occupation Mode) : ℝ :=
  n.sum fun i k => (k : ℝ) * ε i

omit [DecidableEq Mode] in
theorem freeEigenvalue_add (ε : Mode → ℝ) (m n : Occupation Mode) :
    freeEigenvalue ε (m + n) = freeEigenvalue ε m + freeEigenvalue ε n :=
  Finsupp.sum_add_index' (fun i => by simp) (fun i k1 k2 => by push_cast; ring)

omit [DecidableEq Mode] in
theorem freeEigenvalue_singleOccupation (ε : Mode → ℝ) (i : Mode) :
    freeEigenvalue ε (singleOccupation i) = ε i := by
  simp [freeEigenvalue, singleOccupation]

omit [DecidableEq Mode] in
theorem freeEigenvalue_createOccupation (ε : Mode → ℝ) (i : Mode) (n : Occupation Mode) :
    freeEigenvalue ε (createOccupation i n) = freeEigenvalue ε n + ε i := by
  rw [createOccupation, freeEigenvalue_add, freeEigenvalue_singleOccupation]

omit [DecidableEq Mode] in
theorem freeEigenvalue_removeOccupation_of_pos {ε : Mode → ℝ} {i : Mode} {n : Occupation Mode}
    (h : n i ≠ 0) :
    freeEigenvalue ε (removeOccupation i n) = freeEigenvalue ε n - ε i := by
  have heq := freeEigenvalue_createOccupation ε i (removeOccupation i n)
  rw [createOccupation_removeOccupation_of_pos h] at heq
  linarith

/-! ## The free bosonic Hamiltonian -/

/-- **The free bosonic Hamiltonian**, diagonal in the occupation-number basis with eigenvalue
`freeEigenvalue ε n`. -/
noncomputable def freeHamiltonian (ε : Mode → ℝ) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Finsupp.lift (FockSpaceBosonic Mode) ℂ (Occupation Mode)
    fun n => (freeEigenvalue ε n : ℂ) • basisState n

theorem freeHamiltonian_basisState (ε : Mode → ℝ) (n : Occupation Mode) :
    freeHamiltonian ε (basisState n) = (freeEigenvalue ε n : ℂ) • basisState n := by
  change Finsupp.lift _ ℂ _ (fun n => (freeEigenvalue ε n : ℂ) • basisState n)
    (Finsupp.single n 1) = (freeEigenvalue ε n : ℂ) • basisState n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-! ## The algebraic diagonal realization of `e^{τH₀}` -/

/-- **The algebraic, basis-diagonal realization of `e^{τH₀}`** for the free Hamiltonian: the
generic `Common.diagonalEvolution`, specialized to `freeEigenvalue ε`. No operator exponential or
topological completion of `FockSpaceBosonic Mode` is constructed — this is well-defined purely
because `freeHamiltonian` is diagonal in the `basisState` eigenbasis. -/
noncomputable def imaginaryTimeEvolveFree (ε : Mode → ℝ) (τ : ℝ) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Common.diagonalEvolution (freeEigenvalue ε) τ

theorem imaginaryTimeEvolveFree_basisState (ε : Mode → ℝ) (τ : ℝ) (n : Occupation Mode) :
    imaginaryTimeEvolveFree ε τ (basisState n) =
      Complex.exp ((τ * freeEigenvalue ε n : ℝ) : ℂ) • basisState n := by
  simp only [imaginaryTimeEvolveFree, basisState]
  exact Common.diagonalEvolution_basisState (freeEigenvalue ε) τ n

/-- **`e^{0·H₀} = id`.** -/
@[simp]
theorem imaginaryTimeEvolveFree_zero (ε : Mode → ℝ) :
    imaginaryTimeEvolveFree ε 0 = LinearMap.id :=
  Common.diagonalEvolution_zero (freeEigenvalue ε)

/-- **The one-parameter semigroup law**, `e^{τH₀} ∘ e^{τ'H₀} = e^{(τ+τ')H₀}`. -/
theorem imaginaryTimeEvolveFree_add (ε : Mode → ℝ) (τ τ' : ℝ) :
    (imaginaryTimeEvolveFree ε τ).comp (imaginaryTimeEvolveFree ε τ') =
      imaginaryTimeEvolveFree ε (τ + τ') :=
  Common.diagonalEvolution_add (freeEigenvalue ε) τ τ'

/-- **`e^{τH₀}` and `e^{-τH₀}` are mutually inverse.** -/
@[simp]
theorem imaginaryTimeEvolveFree_comp_neg (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε τ).comp (imaginaryTimeEvolveFree ε (-τ)) = LinearMap.id :=
  Common.diagonalEvolution_comp_neg (freeEigenvalue ε) τ

@[simp]
theorem imaginaryTimeEvolveFree_neg_comp (ε : Mode → ℝ) (τ : ℝ) :
    (imaginaryTimeEvolveFree ε (-τ)).comp (imaginaryTimeEvolveFree ε τ) = LinearMap.id :=
  Common.diagonalEvolution_neg_comp (freeEigenvalue ε) τ

/-! ## The Heisenberg-picture evolution of a general operator -/

/-- **The imaginary-time (Heisenberg-picture) evolution of an operator `A` under the free
Hamiltonian**: `A(τ) := e^{τH₀} A e^{-τH₀}`. -/
noncomputable def imaginaryTimeEvolve (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode :=
  Common.heisenbergEvolve (freeEigenvalue ε) τ A

/-- **At `τ = 0`, imaginary-time evolution is trivial**: `A(0) = A`. -/
@[simp]
theorem imaginaryTimeEvolve_zero (ε : Mode → ℝ)
    (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) :
    imaginaryTimeEvolve ε 0 A = A :=
  Common.heisenbergEvolve_zero (freeEigenvalue ε) A

/-- Unfolds `imaginaryTimeEvolve` back down to `imaginaryTimeEvolveFree`, matching the shape most
proofs below need — `A(τ) := e^{τH₀} A e^{-τH₀}`, applied to a vector. -/
theorem imaginaryTimeEvolve_apply (ε : Mode → ℝ) (τ : ℝ)
    (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode) (x : FockSpaceBosonic Mode) :
    imaginaryTimeEvolve ε τ A x =
      imaginaryTimeEvolveFree ε τ (A (imaginaryTimeEvolveFree ε (-τ) x)) :=
  rfl

/-- **The free Hamiltonian evolves trivially under its own flow**: `H₀(τ) = H₀`, since `H₀` is
diagonal in the very basis `imaginaryTimeEvolveFree` acts on by a scalar. -/
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

/-! ## Evolved creation and annihilation operators -/

/-- **The imaginary-time-evolved annihilation operator**: `a_i(τ) = e^{-τε_i} a_i`. The physical
content of the free-theory Heisenberg equation of motion `d/dτ a_i(τ) = [H₀, a_i(τ)] = -ε_i a_i(τ)`,
proved here directly from the basis-level action rather than by solving that ODE. -/
theorem imaginaryTimeEvolve_annihilate (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
  apply linearMap_ext_basisState
  intro n
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply]
  by_cases hi : n i = 0
  · rw [annihilate_basisState_of_zero hi, smul_zero, map_zero, smul_zero]
  · have hexp : -τ * freeEigenvalue ε n + τ * (freeEigenvalue ε n - ε i) = -τ * ε i := by ring
    have hcast : (-(τ : ℂ)) * (ε i : ℂ) = ((-τ * ε i : ℝ) : ℂ) := by push_cast; ring
    rw [annihilate_basisState_of_pos hi, smul_smul, map_smul, imaginaryTimeEvolveFree_basisState,
      smul_smul, freeEigenvalue_removeOccupation_of_pos hi, mul_right_comm, hcast,
      ← Complex.exp_add, ← Complex.ofReal_add, hexp, smul_smul]

/-- **The imaginary-time-evolved creation operator**: `a_i†(τ) = e^{τε_i} a_i†`. -/
theorem imaginaryTimeEvolve_create (ε : Mode → ℝ) (τ : ℝ) (i : Mode) :
    imaginaryTimeEvolve ε τ (create i) = Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
  apply linearMap_ext_basisState
  intro n
  have hexp : -τ * freeEigenvalue ε n + τ * (freeEigenvalue ε n + ε i) = τ * ε i := by ring
  have hcast : (τ : ℂ) * (ε i : ℂ) = ((τ * ε i : ℝ) : ℂ) := by push_cast; ring
  rw [imaginaryTimeEvolve_apply,
    imaginaryTimeEvolveFree_basisState, map_smul, LinearMap.smul_apply, create_basisState_eq,
    smul_smul, map_smul, imaginaryTimeEvolveFree_basisState, smul_smul,
    freeEigenvalue_createOccupation, mul_right_comm, hcast, ← Complex.exp_add,
    ← Complex.ofReal_add, hexp, smul_smul]

end Bosonic
end SecondQuantization
