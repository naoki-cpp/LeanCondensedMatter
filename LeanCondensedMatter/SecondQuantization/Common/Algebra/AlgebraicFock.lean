import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

set_option linter.style.header false

/-!
# The algebraic Fock space, generic over the occupation-state type

Shared infrastructure for the fermionic and bosonic algebraic Fock-space implementations
(`notes/roadmaps/second-quantization.md`): both `Fermionic.OccupationFock Mode` (basis
`Fermionic.Occupation Mode := Finset Mode`) and `Bosonic.FockSpace Mode` (basis
`Bosonic.Occupation Mode := Mode →₀ ℕ`) are the free `ℂ`-vector space on their respective occupation-state
type — finite `ℂ`-linear combinations of basis states, no completion, no inner product. That shape
doesn't depend on which occupation-state type is used, so it's extracted here as
`AlgebraicFock Config` for an arbitrary `Config`, with `Fermionic`/`Bosonic` free to keep their own
concrete `Config` (`Fermionic.Occupation Mode`/`Bosonic.Occupation Mode`) — this file does not unify those
types themselves, only the vector-space construction built on top of whichever one is supplied.

`matrixCoeff`/`diagonalCoeff` give the common coordinate-evaluation API: `A (basisState n) m`, a
coefficient, not an inner product — `AlgebraicFock Config` has none.
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

/-- The canonical basis states of an algebraic Fock space are linearly independent. -/
theorem basisState_linearIndependent {Config : Type*} :
    LinearIndependent ℂ (basisState : Config → AlgebraicFock Config) := by
  change LinearIndependent ℂ (fun c => Finsupp.single c (1 : ℂ))
  exact Finsupp.basisSingleOne.linearIndependent

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

/-- `matrixCoeff` at fixed coordinates, bundled as a complex-linear functional of the operator. -/
noncomputable def matrixCoeffLinear {Config : Type*} (m n : Config) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) →ₗ[ℂ] ℂ :=
  (Finsupp.lapply m).comp (LinearMap.applyₗ (basisState n))

@[simp]
theorem matrixCoeffLinear_apply {Config : Type*} (m n : Config)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    matrixCoeffLinear m n A = matrixCoeff A m n :=
  rfl

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
  simpa only [matrixCoeffLinear_apply, smul_eq_mul] using
    (matrixCoeffLinear m n).map_smul c A

/-- `matrixCoeff` is linear in its operator argument: addition. -/
theorem matrixCoeff_add {Config : Type*}
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A + B) m n = matrixCoeff A m n + matrixCoeff B m n := by
  simpa only [matrixCoeffLinear_apply] using (matrixCoeffLinear m n).map_add A B

/-- **Diagonal matrix coefficients.** If `A` acts on `basisState n` as `c • basisState n`, the
`(n, n)` matrix coefficient is exactly `c`. -/
theorem matrixCoeff_of_smul_basisState {Config : Type*}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {n : Config} {c : ℂ} (h : A (basisState n) = c • basisState n) :
    matrixCoeff A n n = c := by
  change A (basisState n) n = c
  rw [h, smul_basisState_apply_self]

/-- **Two operators agreeing on every matrix coefficient are equal.** -/
theorem matrixCoeff_ext {Config : Type*}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : ∀ m n, matrixCoeff A m n = matrixCoeff B m n) : A = B := by
  apply linearMap_ext_basisState
  intro n
  apply Finsupp.ext
  intro m
  exact h m n

/-- **`matrixCoeff` under composition, as a sum over `B`'s finite support**:
`(AB)_{mn} = Σ_{k ∈ supp(B|n⟩)} A_{mk} B_{kn}`. This holds for arbitrary `Config`, because an
`AlgebraicFock Config` vector is finitely supported even when `Config` itself is infinite. -/
theorem matrixCoeff_comp_support {Config : Type*}
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n =
      ∑ k ∈ (B (basisState n)).support, matrixCoeff A m k * matrixCoeff B k n := by
  have hx : B (basisState n) =
      ∑ k ∈ (B (basisState n)).support, matrixCoeff B k n • basisState k := by
    conv_lhs => rw [← Finsupp.sum_single (B (basisState n))]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => (Finsupp.smul_single_one k _).symm
  rw [matrixCoeff, LinearMap.comp_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`matrixCoeff` under composition is ordinary matrix multiplication** on a finite
configuration type: `(AB)_{mn} = Σₖ A_{mk} B_{kn}`. -/
theorem matrixCoeff_comp {Config : Type*} [Fintype Config]
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑ k : Config, matrixCoeff A m k * matrixCoeff B k n := by
  rw [matrixCoeff_comp_support]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hz : matrixCoeff B k n = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.mpr h)
  rw [hz, mul_zero]

/-! ## Basis-diagonal operators

A single generic constructor for operators that act as a scalar multiple of each basis vector —
the common shape behind `Common.diagonalEvolution` (`e^{τ·energy}` eigenvalues),
`Fermionic.totalNumberOperator`/`freeHamiltonian`/`interactionHamiltonian` (occupation-dependent
eigenvalues), and `Fermionic.occupationProjector` (indicator eigenvalues). Extracting this once
lets each of those be stated as a `diagonalOperator` specialization, sharing the same
composition/matrix-coefficient/injectivity lemmas rather than re-proving them per call site. -/

private noncomputable def diagonalOperatorLinear {Config : Type*} (a : Config → ℂ) :
    AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config :=
  Finsupp.lift (AlgebraicFock Config) ℂ Config fun c => a c • basisState c

@[simp]
private theorem diagonalOperatorLinear_basisState {Config : Type*} (a : Config → ℂ) (c : Config) :
    diagonalOperatorLinear a (basisState c) = a c • basisState c := by
  change Finsupp.lift _ ℂ _ (fun c => a c • basisState c) (Finsupp.single c 1) = a c • basisState c
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- Basis-diagonal operators form the canonical representation of the pointwise function algebra
`Config → ℂ` on the algebraic Fock space. -/
noncomputable def diagonalOperator {Config : Type*} :
    (Config → ℂ) →ₐ[ℂ] (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) where
  toFun := diagonalOperatorLinear
  map_zero' := by
    apply linearMap_ext_basisState
    intro c
    simp
  map_one' := by
    apply linearMap_ext_basisState
    intro c
    simp
  map_add' := by
    intro a b
    apply linearMap_ext_basisState
    intro c
    simp [add_smul]
  map_mul' := by
    intro a b
    rw [Module.End.mul_eq_comp]
    apply linearMap_ext_basisState
    intro c
    simp [smul_smul, mul_comm]
  commutes' := by
    intro k
    apply linearMap_ext_basisState
    intro c
    simp

@[simp]
theorem diagonalOperator_basisState {Config : Type*} (a : Config → ℂ) (c : Config) :
    diagonalOperator a (basisState c) = a c • basisState c :=
  diagonalOperatorLinear_basisState a c

/-- A basis-diagonal operator rescales each coordinate independently. -/
theorem diagonalOperator_apply {Config : Type*} (a : Config → ℂ)
    (x : AlgebraicFock Config) (c : Config) :
    diagonalOperator a x c = a c * x c := by
  let eval : AlgebraicFock Config →ₗ[ℂ] ℂ := Finsupp.lapply c
  have hmap : eval.comp (diagonalOperator a) = a c • eval := by
    apply Finsupp.lhom_ext
    intro i b
    have hb : (Finsupp.single i b : AlgebraicFock Config) = b • basisState i :=
      (Finsupp.smul_single_one i b).symm
    rw [hb, LinearMap.comp_apply, map_smul, diagonalOperator_basisState, map_smul,
      LinearMap.smul_apply]
    by_cases h : i = c
    · subst i
      simp [eval, basisState, mul_comm]
    · simp [eval, basisState, h]
  have hx := congrArg (fun L => L x) hmap
  simpa only [eval, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
    smul_eq_mul] using hx

/-- **`diagonalOperator` turns pointwise multiplication into composition**: `[c•A, d•B]`-style
constructions on diagonal operators reduce to plain scalar arithmetic on their eigenvalues. -/
theorem diagonalOperator_comp {Config : Type*} (a b : Config → ℂ) :
    (diagonalOperator a).comp (diagonalOperator b) = diagonalOperator (fun c => a c * b c) := by
  have h := map_mul (diagonalOperator (Config := Config)) a b
  rw [Module.End.mul_eq_comp] at h
  exact h.symm

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
    Function.Injective (diagonalOperator (Config := Config)) := by
  intro a b hab
  funext c
  have h := congrArg (fun A => matrixCoeff A c c) hab
  simpa [matrixCoeff_diagonalOperator] using h

end Common
end SecondQuantization
