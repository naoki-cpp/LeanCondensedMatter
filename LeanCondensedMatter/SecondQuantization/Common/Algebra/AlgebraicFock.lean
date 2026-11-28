import LeanCondensedMatter.Analysis.Algebra.FinsuppDiagonal
import LeanCondensedMatter.Analysis.Algebra.FinsuppCoordinates
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# Algebraic Fock space over an occupation-state type

`AlgebraicFock Config` is the free `ℂ`-vector space on a configuration type `Config`, represented
by finitely supported complex linear combinations of basis states. The construction is independent
of the particular fermionic or bosonic occupation type used as `Config`.

This module provides canonical basis states, basis extensionality for linear maps, and
`matrixCoeff` as coordinate evaluation. These coefficients are not inner
products: the algebraic Fock space in this module has no Hilbert-space completion or inner-product
structure.
-/

namespace SecondQuantization
namespace Common

/-- **The algebraic Fock space** over an occupation-state type `Config`: the free `ℂ`-vector space
on `Config`, i.e. finite `ℂ`-linear combinations of basis states. An `abbrev` so `Config →₀ ℂ`'s
own `AddCommGroup`/`Module ℂ` instances transfer automatically. -/
abbrev AlgebraicFock (Config : Type*) := Config →₀ ℂ

/-- **The basis vector** corresponding to occupation state `c`. -/
noncomputable def basisState {Config : Type*} (c : Config) : AlgebraicFock Config :=
  Finsupp.single c 1

@[simp]
theorem basisState_ne_zero {Config : Type*} (c : Config) :
    (basisState c : AlgebraicFock Config) ≠ 0 :=
  Finsupp.single_ne_zero.2 one_ne_zero

/-- Two linear maps out of `AlgebraicFock Config` into any complex module that agree on every basis
state are equal. -/
theorem linearMap_ext_basisState {Config W : Type*} [AddCommGroup W] [Module ℂ W]
    {f g : AlgebraicFock Config →ₗ[ℂ] W}
    (h : ∀ c, f (basisState c) = g (basisState c)) : f = g := by
  apply Finsupp.basisSingleOne.ext
  intro c
  simpa only [Finsupp.coe_basisSingleOne, basisState] using h c

@[simp]
theorem smul_basisState_apply_self {Config : Type*} (c : ℂ) (n : Config) :
    (c • basisState n : AlgebraicFock Config) n = c := by
  simp [basisState]

/-- **The `m`-coefficient of `A (basisState n)`** — a coordinate evaluation, not an inner product.
-/
noncomputable def matrixCoeff {Config : Type*}
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) : ℂ :=
  A (basisState n) m

/-- `matrixCoeff` at fixed coordinates, bundled as a complex-linear functional of the operator. -/
noncomputable def matrixCoeffLinear {Config : Type*} (m n : Config) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  (Finsupp.lapply m).comp (LinearMap.applyₗ (basisState n))

@[simp]
theorem matrixCoeffLinear_apply {Config : Type*} (m n : Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    matrixCoeffLinear m n A = matrixCoeff A m n :=
  rfl

open scoped Classical in
/-- **Matrix coefficients of a one-basis-state image.** If `A` sends `basisState n` to
`c • basisState k`, its `(m, n)` coefficient is `c` at `m = k` and `0` elsewhere. -/
theorem matrixCoeff_eq_ite_of_basisState_smul {Config : Type*}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {m n k : Config} {c : ℂ}
    (hA : A (basisState n) = c • basisState k) :
    matrixCoeff A m n = if m = k then c else 0 := by
  rw [matrixCoeff, hA]
  split_ifs with h
  · subst m
    exact smul_basisState_apply_self c k
  · simp [basisState, Ne.symm h]

open scoped Classical in
/-- The identity operator has the Kronecker-delta matrix in the canonical basis. -/
theorem matrixCoeff_id {Config : Type*} (m n : Config) :
    matrixCoeff (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) m n =
      if m = n then 1 else 0 := by
  apply matrixCoeff_eq_ite_of_basisState_smul
  rw [LinearMap.id_apply, one_smul]

/-- **Two operators agreeing on every matrix coefficient are equal.** -/
theorem matrixCoeff_ext {Config : Type*}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : ∀ m n, matrixCoeff A m n = matrixCoeff B m n) : A = B := by
  apply linearMap_ext_basisState
  intro n
  apply Finsupp.ext
  intro m
  exact h m n

/-- **`matrixCoeff` under composition is ordinary matrix multiplication** on a finite
configuration type: `(AB)_{mn} = Σₖ A_{mk} B_{kn}`. -/
theorem matrixCoeff_comp {Config : Type*} [Fintype Config]
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑ k : Config, matrixCoeff A m k * matrixCoeff B k n := by
  exact Finsupp.linearMap_apply_eq_finsetSum_of_support_subset A (B (basisState n))
    Finset.univ (Finset.subset_univ _) m

@[simp]
theorem diagonalOperator_basisState {Config : Type*} (a : Config → ℂ) (c : Config) :
    Finsupp.diagonalOperator a (basisState c) = a c • basisState c :=
  Finsupp.diagonalOperator_single a c

open scoped Classical in
theorem matrixCoeff_diagonalOperator {Config : Type*} (a : Config → ℂ) (m n : Config) :
    matrixCoeff (Finsupp.diagonalOperator a) m n = if m = n then a n else 0 :=
  matrixCoeff_eq_ite_of_basisState_smul (m := m) (diagonalOperator_basisState a n)

end Common
end SecondQuantization
