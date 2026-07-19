import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock

set_option linter.style.header false

/-!
# Finite weighted traces and normalized diagonal functionals, generic over the occupation-state type

Generalizes `Fermionic/WeightedDiagonalFunctional.lean`'s finite-mode-set trace, weighted trace,
total weight, and normalized weighted diagonal functional to an arbitrary occupation-state type
`Config` — the construction never used anything fermion-specific (Pauli exclusion, the `Finset
Mode` representation, or any statistics constant), only `matrixCoeff`/`basisState` on
`AlgebraicFock Config` and `[Fintype Config]` for the finite sum. Extracting it here lets a future
Bloch–de Dominicis induction (and the bosonic line) share one definition and one set of linearity
lemmas instead of duplicating them per statistics.

As in `Fermionic/WeightedDiagonalFunctional.lean`, the weight `w : Config → ℂ` here is
*arbitrary* — not yet the genuine Gibbs weight `e^{-βE(n)}` — so `normalizedWeightedDiagonal` is a
genuine thermal (Gibbs-state) expectation only once `w` is specialized to a positive Boltzmann
weight with `weightSum w ≠ 0`.

`Fermionic/WeightedDiagonalFunctional.lean` keeps its own `weightedTrace`/`weightSum`/
`normalizedWeightedDiagonal`/`traceFock` names as thin specializations of the definitions here
(`Config := FermionOccupation Mode`), so existing fermionic call sites are unaffected.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-! ## Diagonal matrix coefficients -/

/-- **Diagonal matrix coefficients.** If `A` acts on `basisState n` as `c • basisState n`, the
`(n, n)` matrix coefficient is exactly `c`. -/
theorem matrixCoeff_of_smul_basisState {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {n : Config} {c : ℂ} (h : A (basisState n) = c • basisState n) :
    matrixCoeff A n n = c := by
  change A (basisState n) n = c
  rw [h, smul_basisState_apply_self]

variable [Fintype Config]

/-! ## Traces and weighted sums -/

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. -/
noncomputable def traceFock (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, matrixCoeff A n n

/-- **The weighted trace**, `Tr_w A := Σₙ w(n) ⟨n| A |n⟩` — the un-normalized weighted diagonal
functional of `A` against the weight `w`. It becomes the un-normalized thermal weighted trace only
for a Gibbs/Boltzmann weight. -/
noncomputable def weightedTrace (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, w n * matrixCoeff A n n

/-- **The total weight** of a weight function `w`, `weightSum(w) := ∑ₙ w(n)`. `w` is an arbitrary
`Config → ℂ` here, not necessarily a genuine Boltzmann weight. -/
noncomputable def weightSum (w : Config → ℂ) : ℂ :=
  ∑ n : Config, w n

/-- **The normalized weighted diagonal functional** of `A` against `w`, `Tr_w(A) / weightSum(w)`.
It is a genuine thermal (Gibbs-state) expectation only once `w` is specialized to a positive
Boltzmann weight with `weightSum(w) ≠ 0`. For a general complex `w` this is simply a `w`-weighted,
`weightSum(w)`-normalized diagonal functional, with no guarantee of positivity, reality, or a
Gibbs-state interpretation. -/
noncomputable def normalizedWeightedDiagonal (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  weightedTrace w A / weightSum w

/-! ## Linearity of `weightedTrace`/`normalizedWeightedDiagonal` in the operator argument -/

theorem weightedTrace_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simp only [weightedTrace, matrixCoeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem weightedTrace_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B := by
  simp only [weightedTrace, matrixCoeff_add, mul_add]
  exact Finset.sum_add_distrib

theorem normalizedWeightedDiagonal_smul (c : ℂ) (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (c • A) = c * normalizedWeightedDiagonal w A := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, weightedTrace_smul, mul_div_assoc]

theorem normalizedWeightedDiagonal_add (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A + B) =
      normalizedWeightedDiagonal w A + normalizedWeightedDiagonal w B := by
  rw [normalizedWeightedDiagonal, normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    weightedTrace_add, add_div]

theorem normalizedWeightedDiagonal_neg (w : Config → ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (-A) = -normalizedWeightedDiagonal w A := by
  rw [show (-A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, normalizedWeightedDiagonal_smul, neg_one_mul]

theorem normalizedWeightedDiagonal_sub (w : Config → ℂ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonal w (A - B) =
      normalizedWeightedDiagonal w A - normalizedWeightedDiagonal w B := by
  change normalizedWeightedDiagonal w (A + -B) =
    normalizedWeightedDiagonal w A + -normalizedWeightedDiagonal w B
  rw [normalizedWeightedDiagonal_add, normalizedWeightedDiagonal_neg]

/-! ## Weighted traces of the identity -/

@[simp]
theorem traceFock_id : traceFock (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) =
    (Fintype.card Config : ℂ) := by
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [traceFock, h]

/-- **The weighted trace of the identity is the partition function itself**,
`Tr_w(id) = Σₙ w(n) = weightSum(w)`. -/
theorem weightedTrace_id (w : Config → ℂ) :
    weightedTrace w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = weightSum w := by
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [weightedTrace, weightSum, h]

/-- **The normalized weighted functional of the identity is `1`**,
`⟨id⟩_w = weightSum(w)/weightSum(w) = 1`, given a nonzero total weight. For a Gibbs/Boltzmann
weight this is the corresponding Gibbs statement. -/
theorem normalizedWeightedDiagonal_id (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    normalizedWeightedDiagonal w (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) = 1 := by
  rw [normalizedWeightedDiagonal, weightedTrace_id, div_self hw]

end Common
end SecondQuantization
