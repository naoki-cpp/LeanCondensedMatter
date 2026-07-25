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

/-- `matrixCoeff` is linear in its operator argument: scaling. -/
theorem matrixCoeff_smul {Config : Type*} (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (c • A) m n = c * matrixCoeff A m n := by
  simp [matrixCoeff]

/-- `matrixCoeff` is linear in its operator argument: addition. -/
theorem matrixCoeff_add {Config : Type*}
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A + B) m n = matrixCoeff A m n + matrixCoeff B m n := by
  simp [matrixCoeff]

/-- `matrixCoeff` is linear in its operator argument: finite sums. -/
theorem matrixCoeff_sum {Config ι : Type*} (s : Finset ι)
    (f : ι → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (∑ i ∈ s, f i) m n = ∑ i ∈ s, matrixCoeff (f i) m n := by
  simp [matrixCoeff]

/-! ## Basis-diagonal operators

A single generic constructor for operators that act as a scalar multiple of each basis vector —
the common shape behind `Common.diagonalEvolution` (`e^{τ·energy}` eigenvalues),
`Fermionic.totalNumberOperator`/`freeHamiltonian`/`interactionHamiltonian` (occupation-dependent
eigenvalues), and `Fermionic.occupationProjector` (indicator eigenvalues). Extracting this once
lets each of those be stated as a `diagonalOperator` specialization, sharing the same
composition/matrix-coefficient/injectivity lemmas rather than re-proving them per call site. -/

/-- **The basis-diagonal operator with eigenvalues `a`**: acts as `a c • basisState c` on each
basis vector, extended linearly via `Finsupp.lift`. -/
noncomputable def diagonalOperator {Config : Type*} (a : Config → ℂ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config fun c => a c • basisState c

@[simp]
theorem diagonalOperator_basisState {Config : Type*} (a : Config → ℂ) (c : Config) :
    diagonalOperator a (basisState c) = a c • basisState c := by
  change Finsupp.lift _ ℂ _ (fun c => a c • basisState c) (Finsupp.single c 1) = a c • basisState c
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

theorem diagonalOperator_zero {Config : Type*} :
    diagonalOperator (fun _ : Config => (0 : ℂ)) = 0 :=
  linearMap_ext_basisState fun c => by simp

theorem diagonalOperator_one {Config : Type*} :
    diagonalOperator (fun _ : Config => (1 : ℂ)) = LinearMap.id :=
  linearMap_ext_basisState fun c => by simp

theorem diagonalOperator_add {Config : Type*} (a b : Config → ℂ) :
    diagonalOperator (fun c => a c + b c) = diagonalOperator a + diagonalOperator b :=
  linearMap_ext_basisState fun c => by simp [add_smul]

theorem diagonalOperator_smul {Config : Type*} (k : ℂ) (a : Config → ℂ) :
    diagonalOperator (fun c => k * a c) = k • diagonalOperator a :=
  linearMap_ext_basisState fun c => by simp [smul_smul]

/-- **`diagonalOperator` turns pointwise multiplication into composition**: `[c•A, d•B]`-style
constructions on diagonal operators reduce to plain scalar arithmetic on their eigenvalues. -/
theorem diagonalOperator_comp {Config : Type*} (a b : Config → ℂ) :
    (diagonalOperator a).comp (diagonalOperator b) = diagonalOperator (fun c => a c * b c) :=
  linearMap_ext_basisState fun c => by simp [smul_smul, mul_comm]

theorem diagonalOperator_comm {Config : Type*} (a b : Config → ℂ) :
    (diagonalOperator a).comp (diagonalOperator b) =
      (diagonalOperator b).comp (diagonalOperator a) := by
  rw [diagonalOperator_comp, diagonalOperator_comp]
  congr 1
  funext c
  ring

open scoped Classical in
theorem matrixCoeff_diagonalOperator {Config : Type*} (a : Config → ℂ) (m n : Config) :
    matrixCoeff (diagonalOperator a) m n = if m = n then a n else 0 := by
  rw [matrixCoeff, diagonalOperator_basisState]
  split_ifs with h
  · subst h; simp
  · exact smul_basisState_apply_of_ne (a n) (Ne.symm h)

open scoped Classical in
/-- **`diagonalOperator` is injective in its eigenvalue function** — two diagonal operators agree
only if their eigenvalues agree everywhere, read off via `matrixCoeff_diagonalOperator` at the
diagonal `m = n`. -/
theorem diagonalOperator_injective {Config : Type*} :
    Function.Injective
      (diagonalOperator : (Config → ℂ) → AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
  intro a b hab
  funext c
  have h := congrArg (fun A => matrixCoeff A c c) hab
  simpa [matrixCoeff_diagonalOperator] using h

end Common
end SecondQuantization
