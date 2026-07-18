import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# The algebraic Fock space, generic over the occupation-state type

Shared infrastructure for Track D's fermionic and bosonic lines
(`notes/roadmaps/second-quantization.md`): both `FockSpaceFermionic Mode` (basis
`FermionOccupation Mode := Finset Mode`) and `FockSpaceBosonic Mode` (basis
`Occupation Mode := Mode →₀ ℕ`) are the free `ℂ`-vector space on their respective occupation-state
type — finite `ℂ`-linear combinations of basis states, no completion, no inner product. That shape
doesn't depend on which occupation-state type is used, so it's extracted here as
`AlgebraicFock Config` for an arbitrary `Config`, with `Fermionic`/`Bosonic` free to keep their own
concrete `Config` (`FermionOccupation Mode`/`Occupation Mode`) — this file does not unify those
types themselves, only the vector-space construction built on top of whichever one is supplied.

`matrixCoeff`/`diagonalCoeff` generalize the coordinate-evaluation APIs each statistics line
already has under its own name (`Fermionic.matrixCoeff`, `Bosonic.diagonalCoeff`): `A (basisState
n) m`, a coefficient, not an inner product — `AlgebraicFock Config` has none.
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

theorem basisState_injective {Config : Type*} :
    Function.Injective (basisState : Config → AlgebraicFock Config) :=
  fun _ _ h => Finsupp.single_left_injective one_ne_zero h

/-- Two linear maps out of `AlgebraicFock Config` that agree on every basis state are equal. -/
theorem linearMap_ext_basisState {Config : Type*}
    {f g : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : ∀ c, f (basisState c) = g (basisState c)) : f = g := by
  apply Finsupp.lhom_ext
  intro c b
  have hb : (Finsupp.single c b : AlgebraicFock Config) = b • basisState c :=
    (Finsupp.smul_single_one c b).symm
  rw [hb, map_smul, map_smul, h]

@[simp]
theorem smul_basisState_apply_self {Config : Type*} (c : ℂ) (n : Config) :
    (c • basisState n : AlgebraicFock Config) n = c := by
  simp [basisState]

/-- The `n`-coefficient of a scalar multiple of a *different* basis state `m ≠ n` is always `0` —
the algebraic core of "particle-number-changing operators have vanishing diagonal matrix
coefficients" (e.g. same-type creation/annihilation contractions). -/
theorem smul_basisState_apply_of_ne {Config : Type*} (c : ℂ) {m n : Config} (h : m ≠ n) :
    (c • basisState m : AlgebraicFock Config) n = 0 := by
  simp [basisState, h]

/-- **The `m`-coefficient of `A (basisState n)`** — a coordinate evaluation, not an inner product.
-/
noncomputable def matrixCoeff {Config : Type*}
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) : ℂ :=
  A (basisState n) m

/-- **The diagonal coefficient of `A (basisState n)`**, `matrixCoeff A n n`. -/
noncomputable def diagonalCoeff {Config : Type*}
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) : ℂ :=
  matrixCoeff A n n

theorem diagonalCoeff_eq_matrixCoeff {Config : Type*}
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (n : Config) :
    diagonalCoeff A n = matrixCoeff A n n :=
  rfl

end Common
end SecondQuantization
