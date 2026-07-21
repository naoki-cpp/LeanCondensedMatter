import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.WeightedDiagonalFunctional
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

/-!
# Imaginary-time evolution under a diagonal free Hamiltonian, generic over the basis type

Shared infrastructure for Track D's fermionic and bosonic lines
(`notes/roadmaps/second-quantization.md`): both `Fermionic.ImaginaryTimeEvolution.lean` and
`Bosonic.ImaginaryTimeEvolution.lean` construct `e^{τH₀}` for a free Hamiltonian that is diagonal
in the occupation-number basis with some real eigenvalue `E(n)` — `Σᵢ∈n ε(i)` for fermions,
`Σᵢ n(i)·ε(i)` for bosons — and both prove the exact same shape of facts about it: the basis-level
action `|n⟩ ↦ exp(τ E(n))|n⟩`, the one-parameter semigroup law, mutual inversion of `e^{τH₀}` and
`e^{-τH₀}`, and the algebraic Heisenberg-type evolution `A(τ) := e^{τH₀} A e^{-τH₀}` of a
general operator.
None of that depends on which occupation-state type or eigenvalue formula produced `E`, so it's
extracted here as `diagonalEvolution energy τ` on `AlgebraicFock Config`, generic over `Config`
and an arbitrary real-valued `energy : Config → ℝ`.

**This is an algebraic, basis-diagonal realization of `e^{τH₀}`, not an operator exponential**:
`diagonalEvolution` is defined directly from `energy`'s value on each basis state, not derived from
an operator-valued `Complex.exp` of some `H₀ : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config`
(no topological completion of `AlgebraicFock Config` exists to make such an operator exponential
meaningful yet). See `Bosonic.freeHamiltonian`/`Bosonic.freeHamiltonian_basisState` for how the
bosonic line relates the two for its own `energy := freeEigenvalue ε`.

Both `Fermionic.imaginaryTimeEvolveFree`/`imaginaryTimeEvolve` and
`Bosonic.imaginaryTimeEvolveFree`/`imaginaryTimeEvolve` are now specialized wrappers around
`diagonalEvolution`/`heisenbergEvolve` here (`fermionEnergy`/`freeEigenvalue` supplying `energy`),
so the semigroup/inversion/`A(0) = A` facts are proved once, in this file.
-/

namespace SecondQuantization
namespace Common

open scoped Classical

variable {Config : Type*}

/-- **`e^{τH₀}`, on a basis state**, defined directly from `energy c` rather than as an operator
exponential: `exp(τ · energy c) • |c⟩`. -/
noncomputable def diagonalEvolutionBasis (energy : Config → ℝ) (τ : ℝ) (c : Config) :
    AlgebraicFock Config :=
  Complex.exp ((τ * energy c : ℝ) : ℂ) • basisState c

/-- **The algebraic, basis-diagonal realization of `e^{τH₀}`** for a free Hamiltonian diagonal in
the `basisState` eigenbasis with eigenvalue `energy`, extended linearly from
`diagonalEvolutionBasis`. -/
noncomputable def diagonalEvolution (energy : Config → ℝ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config (diagonalEvolutionBasis energy τ)

theorem diagonalEvolution_basisState (energy : Config → ℝ) (τ : ℝ) (c : Config) :
    diagonalEvolution energy τ (basisState c) =
      Complex.exp ((τ * energy c : ℝ) : ℂ) • basisState c := by
  change Finsupp.lift _ ℂ _ (diagonalEvolutionBasis energy τ) (Finsupp.single c 1) =
    diagonalEvolutionBasis energy τ c
  simp [Finsupp.lift_apply, Finsupp.sum_single_index, diagonalEvolutionBasis]

/-- **`e^{0·H₀} = id`.** -/
@[simp]
theorem diagonalEvolution_zero (energy : Config → ℝ) :
    diagonalEvolution energy 0 = LinearMap.id := by
  apply linearMap_ext_basisState
  intro c
  simp [diagonalEvolution_basisState]

/-- **The one-parameter semigroup law**, `e^{τH₀} ∘ e^{τ'H₀} = e^{(τ+τ')H₀}`. -/
theorem diagonalEvolution_add (energy : Config → ℝ) (τ τ' : ℝ) :
    (diagonalEvolution energy τ).comp (diagonalEvolution energy τ') =
      diagonalEvolution energy (τ + τ') := by
  apply linearMap_ext_basisState
  intro c
  rw [LinearMap.comp_apply, diagonalEvolution_basisState, map_smul,
    diagonalEvolution_basisState, diagonalEvolution_basisState, smul_smul,
    ← Complex.exp_add, ← Complex.ofReal_add]
  congr 2
  ring_nf

/-- **`e^{τH₀}` and `e^{-τH₀}` are mutually inverse.** -/
@[simp]
theorem diagonalEvolution_comp_neg (energy : Config → ℝ) (τ : ℝ) :
    (diagonalEvolution energy τ).comp (diagonalEvolution energy (-τ)) = LinearMap.id := by
  rw [diagonalEvolution_add]
  simp

@[simp]
theorem diagonalEvolution_neg_comp (energy : Config → ℝ) (τ : ℝ) :
    (diagonalEvolution energy (-τ)).comp (diagonalEvolution energy τ) = LinearMap.id := by
  rw [diagonalEvolution_add]
  simp

/-! ## Algebraic Heisenberg-type evolution of a general operator -/

/-- **The algebraic imaginary-time (Heisenberg-type) evolution of an operator `A` under the
diagonal free Hamiltonian**: `A(τ) := e^{τH₀} A e^{-τH₀}`. This is the conjugation operation
available on `AlgebraicFock`; it is not a completed-Hilbert-space operator construction. -/
noncomputable def heisenbergEvolve (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  (diagonalEvolution energy τ).comp (A.comp (diagonalEvolution energy (-τ)))

/-- **At `τ = 0`, imaginary-time evolution is trivial**: `A(0) = A`. -/
@[simp]
theorem heisenbergEvolve_zero (energy : Config → ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    heisenbergEvolve energy 0 A = A := by
  simp [heisenbergEvolve]

/-! ## Matrix coefficients -/

/-- **`diagonalEvolution`'s matrix coefficients**: diagonal, `exp(τ · energy n)` on the diagonal
and `0` off it — the algebraic content of "`diagonalEvolution` acts on each basis state by a
scalar". Needed for `matrixCoeff_heisenbergEvolve` below, and (specialized to `energy :=
freeEigenvalue`/`fermionEnergy`, `τ := -β`) for the Gibbs weight's own diagonal matrix entries
(`GibbsExpectation/Core.lean`'s `matrixCoeff_diagonalEvolution`, proved independently there rather
than from this lemma to avoid pulling this file's dependents into that heavier one). -/
theorem matrixCoeff_diagonalEvolution_eq_ite (energy : Config → ℝ) (τ : ℝ) (m n : Config) :
    matrixCoeff (diagonalEvolution energy τ) m n =
      if m = n then Complex.exp ((τ * energy n : ℝ) : ℂ) else 0 := by
  rw [matrixCoeff, diagonalEvolution_basisState]
  by_cases h : m = n
  · simp only [if_pos h]
    rw [← h, smul_basisState_apply_self]
  · simp only [if_neg h]
    exact smul_basisState_apply_of_ne _ (Ne.symm h)

/-- **`heisenbergEvolve`'s matrix coefficients**: `A(τ)`'s `(m, n)` entry is `A`'s own `(m, n)`
entry, rescaled by `exp(τ(energy m - energy n))` — the interaction-picture matrix-coefficient
formula, for an *arbitrary* `A`, not just an eigenoperator of `heisenbergEvolve` (contrast
`diagonalEvolution_comp_eq_smul_comp_diagonalEvolution`'s `hC` hypothesis, which needs `A` to
already be an eigenoperator). Both `matrixCoeff (diagonalEvolution energy τ)` factors collapse the
defining `Finset.sum`s (from `matrixCoeff_comp`) to their single nonzero term. -/
theorem matrixCoeff_heisenbergEvolve [Fintype Config] (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (heisenbergEvolve energy τ A) m n =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff A m n := by
  have hinner : matrixCoeff (A.comp (diagonalEvolution energy (-τ))) m n =
      matrixCoeff A m n * Complex.exp (((-τ) * energy n : ℝ) : ℂ) := by
    rw [matrixCoeff_comp]
    have hstep' : ∀ k, matrixCoeff A m k * matrixCoeff (diagonalEvolution energy (-τ)) k n =
        if k = n then matrixCoeff A m k *
          Complex.exp (((-τ) * energy n : ℝ) : ℂ) else 0 := by
      intro k
      rw [matrixCoeff_diagonalEvolution_eq_ite]
      by_cases h : k = n <;> simp [h]
    simp only [hstep', Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [heisenbergEvolve, matrixCoeff_comp]
  have hstep : ∀ k, matrixCoeff (diagonalEvolution energy τ) m k *
      matrixCoeff (A.comp (diagonalEvolution energy (-τ))) k n =
        if m = k then Complex.exp ((τ * energy k : ℝ) : ℂ) *
          matrixCoeff (A.comp (diagonalEvolution energy (-τ))) k n else 0 := by
    intro k
    rw [matrixCoeff_diagonalEvolution_eq_ite]
    by_cases h : m = k <;> simp [h]
  simp only [hstep, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hinner, mul_comm (matrixCoeff A m n), ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## The KMS-type commutation relation, for an operator with a known eigenvalue shift -/

/-- **The KMS-type relation**: if a linear map `C` picks up an exponential eigenvalue-shift factor
`e^{qτ}` under `heisenbergEvolve` (as every `create`/`annihilate` operator does, with `q` the
eigenvalue shift `∓ε_i`), then `e^{τH₀}` and `C` satisfy `e^{τH₀} C = e^{qτ} C e^{τH₀}` — the exact
statistics-agnostic algebraic ingredient the finite-temperature Bloch–de Dominicis theorem's
KMS-rotation step needs (`ĉ_α e^{-βĤ} = e^{-βξ_α} e^{-βĤ} ĉ_α` in the project's physics reference
notes, `quantum-statistical-mechanics.tex`'s "product-of-KMS-state-and-ladder-op"), obtained purely
by rearranging the already-proved semigroup law and mutual inversion
(`diagonalEvolution_neg_comp`) — no new physical input beyond the eigenvalue-shift hypothesis
`hC`, and in particular no dependence on the concrete occupation-state type or exchange statistics.
Both `Fermionic.imaginaryTimeEvolve_annihilate`/`_create` and
`Bosonic.imaginaryTimeEvolve_annihilate`/`_create` supply exactly this hypothesis (with
`q := -ε i`/`q := ε i` respectively), so this single `Common/` lemma gives the KMS relation for
`create`/`annihilate` in both statistics at once. -/
theorem diagonalEvolution_comp_eq_smul_comp_diagonalEvolution
    (energy : Config → ℝ) (τ q : ℝ) (C : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC : heisenbergEvolve energy τ C = Complex.exp ((q * τ : ℝ) : ℂ) • C) :
    (diagonalEvolution energy τ).comp C =
      Complex.exp ((q * τ : ℝ) : ℂ) • (C.comp (diagonalEvolution energy τ)) := by
  have h := congrArg (fun f => f.comp (diagonalEvolution energy τ)) hC
  rw [heisenbergEvolve, LinearMap.comp_assoc, LinearMap.comp_assoc, diagonalEvolution_neg_comp,
    LinearMap.comp_id, LinearMap.smul_comp] at h
  exact h

end Common
end SecondQuantization
