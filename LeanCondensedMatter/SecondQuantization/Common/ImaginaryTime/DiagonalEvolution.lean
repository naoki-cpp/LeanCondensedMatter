import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# Imaginary-time evolution under a diagonal free Hamiltonian

For any configuration type `Config` and real energy function `energy : Config → ℝ`, this module
defines the basis-diagonal evolution

`|n⟩ ↦ exp(τ E(n)) |n⟩`

on `AlgebraicFock Config`. It proves the one-parameter composition law, mutual inversion of
positive and negative imaginary times, and the algebraic Heisenberg evolution
`A(τ) = e^{τH₀} A e^{-τH₀}`.

This is a direct basis-diagonal construction, not an operator exponential on a completed normed
space. Fermionic and bosonic imaginary-time evolutions specialize it using their respective free
energy functions.
-/

namespace SecondQuantization
namespace Common

open scoped Classical

variable {Config : Type*}

/-- **The algebraic, basis-diagonal realization of `e^{τH₀}`** for a free Hamiltonian diagonal in
the `basisState` eigenbasis with eigenvalue `energy`. It is the specialization of the canonical
`diagonalOperator` representation to eigenvalues `c ↦ exp (τ * energy c)`. -/
noncomputable def diagonalEvolution (energy : Config → ℝ) (τ : ℝ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  diagonalOperator fun c => Complex.exp ((τ * energy c : ℝ) : ℂ)

theorem diagonalEvolution_basisState (energy : Config → ℝ) (τ : ℝ) (c : Config) :
    diagonalEvolution energy τ (basisState c) =
      Complex.exp ((τ * energy c : ℝ) : ℂ) • basisState c :=
  diagonalOperator_basisState _ c

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
  rw [diagonalEvolution, diagonalEvolution, diagonalEvolution, diagonalOperator_comp]
  congr 1
  funext c
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

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

/-- Diagonal evolution as a linear automorphism, with inverse parameter `-τ`. -/
noncomputable def diagonalEvolutionEquiv (energy : Config → ℝ) (τ : ℝ) :
    AlgebraicFock Config ≃ₗ[ℂ] AlgebraicFock Config where
  __ := diagonalEvolution energy τ
  invFun := diagonalEvolution energy (-τ)
  left_inv x := by
    change ((diagonalEvolution energy (-τ)).comp (diagonalEvolution energy τ)) x = x
    rw [diagonalEvolution_neg_comp]
    rfl
  right_inv x := by
    change ((diagonalEvolution energy τ).comp (diagonalEvolution energy (-τ))) x = x
    rw [diagonalEvolution_comp_neg]
    rfl

theorem diagonalEvolutionEquiv_apply (energy : Config → ℝ) (τ : ℝ)
    (x : AlgebraicFock Config) :
    diagonalEvolutionEquiv energy τ x = diagonalEvolution energy τ x :=
  rfl

theorem diagonalEvolutionEquiv_symm_apply (energy : Config → ℝ) (τ : ℝ)
    (x : AlgebraicFock Config) :
    (diagonalEvolutionEquiv energy τ).symm x = diagonalEvolution energy (-τ) x :=
  rfl

private theorem diagonalEvolutionEquiv_trans (energy : Config → ℝ) (s t : ℝ) :
    (diagonalEvolutionEquiv energy s).trans (diagonalEvolutionEquiv energy t) =
      diagonalEvolutionEquiv energy (s + t) := by
  apply LinearEquiv.ext
  intro x
  change ((diagonalEvolution energy t).comp (diagonalEvolution energy s)) x =
    diagonalEvolution energy (s + t) x
  rw [diagonalEvolution_add, add_comm t s]

/-! ## Algebraic Heisenberg-type evolution of a general operator -/

/-- **The algebraic imaginary-time (Heisenberg-type) evolution of operators under the diagonal
free Hamiltonian**, bundled as Mathlib's canonical conjugation algebra equivalence. Applying it to
`A` gives `A(τ) := e^{τH₀} A e^{-τH₀}`. This is an algebraic-Fock construction, not a
completed-Hilbert-space operator exponential. -/
noncomputable def heisenbergEvolve (energy : Config → ℝ) (τ : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) ≃ₐ[ℂ]
      (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :=
  (diagonalEvolutionEquiv energy τ).conjAlgEquiv ℂ

/-- Unbundled composition formula for diagonal Heisenberg conjugation. -/
theorem heisenbergEvolve_eq_comp (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    heisenbergEvolve energy τ A =
      (diagonalEvolution energy τ).comp (A.comp (diagonalEvolution energy (-τ))) := by
  apply LinearMap.ext
  intro x
  rfl

/-- **At `τ = 0`, imaginary-time evolution is trivial**: `A(0) = A`. -/
@[simp]
theorem heisenbergEvolve_zero (energy : Config → ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    heisenbergEvolve energy 0 A = A := by
  rw [heisenbergEvolve_eq_comp]
  simp

/-! ## Matrix coefficients -/

/-- **`diagonalEvolution`'s matrix coefficients**: diagonal, `exp(τ · energy n)` on the diagonal
and `0` off it — the algebraic content of "`diagonalEvolution` acts on each basis state by a
scalar". Specialized to `energy := freeEigenvalue`/`fermionEnergy`, `τ := -β`, the same formula
provides the basis-diagonal Gibbs-weight coefficients. -/
theorem matrixCoeff_diagonalEvolution_eq_ite (energy : Config → ℝ) (τ : ℝ) (m n : Config) :
    matrixCoeff (diagonalEvolution energy τ) m n =
      if m = n then Complex.exp ((τ * energy n : ℝ) : ℂ) else 0 := by
  simpa only [diagonalEvolution] using
    matrixCoeff_diagonalOperator (fun c => Complex.exp ((τ * energy c : ℝ) : ℂ)) m n

/-- **`heisenbergEvolve`'s matrix coefficients**: `A(τ)`'s `(m, n)` entry is `A`'s own `(m, n)`
entry, rescaled by `exp(τ(energy m - energy n))` — the interaction-picture matrix-coefficient
formula, for an arbitrary configuration type. -/
theorem matrixCoeff_heisenbergEvolve (energy : Config → ℝ) (τ : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (heisenbergEvolve energy τ A) m n =
      Complex.exp ((τ * (energy m - energy n) : ℝ) : ℂ) * matrixCoeff A m n := by
  rw [heisenbergEvolve_eq_comp, matrixCoeff, LinearMap.comp_apply,
    LinearMap.comp_apply, diagonalEvolution_basisState, map_smul, diagonalEvolution,
    diagonalOperator_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **`heisenbergEvolve` is a one-parameter semigroup**: `A(s)(t) = A(s + t)`. -/
theorem heisenbergEvolve_heisenbergEvolve (energy : Config → ℝ) (s t : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    heisenbergEvolve energy t (heisenbergEvolve energy s A) =
      heisenbergEvolve energy (s + t) A := by
  change
    (diagonalEvolutionEquiv energy t).conjAlgEquiv ℂ
        ((diagonalEvolutionEquiv energy s).conjAlgEquiv ℂ A) =
      (diagonalEvolutionEquiv energy (s + t)).conjAlgEquiv ℂ A
  rw [← diagonalEvolutionEquiv_trans energy s t]
  apply LinearMap.ext
  intro x
  rfl

/-- Every basis-diagonal operator is fixed by diagonal Heisenberg evolution. -/
theorem heisenbergEvolve_diagonalOperator (energy : Config → ℝ) (τ : ℝ) (a : Config → ℂ) :
    heisenbergEvolve energy τ (diagonalOperator a) = diagonalOperator a := by
  rw [heisenbergEvolve_eq_comp]
  have hcomm :
      (diagonalEvolution energy τ).comp (diagonalOperator a) =
        (diagonalOperator a).comp (diagonalEvolution energy τ) := by
    rw [diagonalEvolution, diagonalOperator_comp, diagonalOperator_comp]
    congr 1
    funext c
    ring
  rw [← LinearMap.comp_assoc, hcomm, LinearMap.comp_assoc,
    diagonalEvolution_comp_neg, LinearMap.comp_id]

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
  rw [heisenbergEvolve_eq_comp, LinearMap.comp_assoc, LinearMap.comp_assoc,
    diagonalEvolution_neg_comp, LinearMap.comp_id, LinearMap.smul_comp] at h
  exact h

end Common
end SecondQuantization
