import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Finite weighted traces and normalized diagonal functionals, generic over the occupation-state type

A statistics-agnostic utility for a *finite* occupation-state type `Config` (`[Fintype Config]`):
generalizes `Fermionic/WeightedDiagonalFunctional.lean`'s finite-mode-set trace, weighted trace,
total weight, and normalized weighted diagonal functional away from `FermionOccupation Mode`
specifically — the construction never used anything fermion-specific (Pauli exclusion, the `Finset
Mode` representation, or any statistics constant), only `matrixCoeff`/`basisState` on
`AlgebraicFock Config` and finiteness of `Config` for the finite sum.

**This is not yet shared with the bosonic line.** `Bosonic.Occupation Mode := Mode →₀ ℕ` is
infinite even for a finite mode set (unbounded occupation per mode), so it does not satisfy
`[Fintype Config]` and cannot instantiate the definitions here. The physical bosonic weighted
trace needs a separate, summability-aware `tsum` construction; it is not an instantiation of this
finite-sum one. The current concrete user of this file is the fermionic finite-mode line
(`Fermionic/WeightedDiagonalFunctional.lean`, below); a common abstract interface over both the
finite-sum and `tsum` constructions, if one turns out to be worth building, is separate future
work.

As in `Fermionic/WeightedDiagonalFunctional.lean`, the weight `w : Config → ℂ` here is
*arbitrary* — not yet the genuine Gibbs weight `e^{-βE(n)}` — so `weightSum w` is only a total
weight, not yet a physical partition function, and `normalizedWeightedDiagonal` is a genuine
thermal (Gibbs-state) expectation only once `w` is specialized to a positive Boltzmann weight with
`weightSum w ≠ 0`.

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

/-! ## Composition of matrix coefficients -/

/-- **`matrixCoeff` under composition, as a sum over `B`'s (finite) support**:
`(AB)_{mn} = Σ_{k ∈ supp(B|n⟩)} A_{mk} B_{kn}`, expanding `B (basisState n)` in the basis and
reading off `A`'s action on each basis vector. Holds for an *arbitrary* `Config` — `AlgebraicFock
Config`'s elements are finitely supported by construction (`Config →₀ ℂ`), independent of whether
`Config` itself is a `Fintype`. This is the form usable on an infinite `Config` such as
`Bosonic.Occupation Mode := Mode →₀ ℕ`. -/
theorem matrixCoeff_comp_support (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (m n : Config) :
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

/-! ## `tsum` diagonal-trace cyclicity, for a possibly-infinite `Config` -/

/-- **The `tsum` diagonal trace is cyclic under a two-operator swap, given absolute
double-summability**: `Σ'ₙ (AB)ₙₙ = Σ'ₙ (BA)ₙₙ`, whenever the bivariate family
`(n, k) ↦ A_{nk} B_{kn}` is (unconditionally) `Summable` over `Config × Config`. Unlike
`traceFock_comp_comm` below, this holds for an *arbitrary* `Config`, finite or not — the
`[Fintype Config]`-specific `traceFock_comp_comm` is the special case where the hypothesis is
automatic (a finite sum is always summable). This is the piece needed for a bosonic analogue of
finite-dimensional trace cyclicity, where `Config := Bosonic.Occupation Mode := Mode →₀ ℕ` is
genuinely infinite even for a finite mode set: an actual instantiation for the free bosonic
Boltzmann weight still needs to establish the summability hypothesis from
`Bosonic/BoltzmannWeightSummable.lean`-style convergence facts, which is not done here. -/
theorem tsum_matrixCoeff_diag_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    ∑' n, matrixCoeff (A.comp B) n n = ∑' n, matrixCoeff (B.comp A) n n := by
  have hrow : ∀ n, (∑' k, matrixCoeff A n k * matrixCoeff B k n) = matrixCoeff (A.comp B) n n := by
    intro n
    rw [matrixCoeff_comp_support]
    exact (hasSum_sum_of_ne_finset_zero
      (s := (B (basisState n)).support)
      (fun k hk => by
        have hz : matrixCoeff B k n = 0 := by
          by_contra hcon; exact hk (Finsupp.mem_support_iff.mpr hcon)
        rw [hz, mul_zero])).tsum_eq
  have hcol : ∀ k, (∑' n, matrixCoeff A n k * matrixCoeff B k n) = matrixCoeff (B.comp A) k k := by
    intro k
    have heq : (fun n => matrixCoeff A n k * matrixCoeff B k n) =
        fun n => matrixCoeff B k n * matrixCoeff A n k := funext fun n => mul_comm _ _
    rw [heq, matrixCoeff_comp_support]
    exact (hasSum_sum_of_ne_finset_zero
      (s := (A (basisState k)).support)
      (fun n hn => by
        have hz : matrixCoeff A n k = 0 := by
          by_contra hcon; exact hn (Finsupp.mem_support_iff.mpr hcon)
        rw [hz, mul_zero])).tsum_eq
  calc ∑' n, matrixCoeff (A.comp B) n n
      = ∑' n, ∑' k, matrixCoeff A n k * matrixCoeff B k n := tsum_congr fun n => (hrow n).symm
    _ = ∑' k, ∑' n, matrixCoeff A n k * matrixCoeff B k n := h.tsum_comm.symm
    _ = ∑' n, matrixCoeff (B.comp A) n n := tsum_congr fun k => hcol k

variable [Fintype Config]

/-! ## Traces and weighted sums -/

/-- **The Fock-space trace** of an operator, `Tr A := Σₙ ⟨n| A |n⟩`. -/
noncomputable def traceFock (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑ n : Config, matrixCoeff A n n

/-! ## `[Fintype Config]` composition and cyclicity — a finite-configuration fact -/

/-- **`matrixCoeff` under composition is ordinary matrix multiplication**, `(AB)_{mn} = Σₖ A_{mk}
B_{kn}` over *all* of `Config`: the `[Fintype Config]` specialization of
`matrixCoeff_comp_support`, extending its support-sum to a `Finset.univ` sum (the extra terms
vanish, since `B (basisState n)` has zero coefficient outside its support). -/
theorem matrixCoeff_comp (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑ k : Config, matrixCoeff A m k * matrixCoeff B k n := by
  rw [matrixCoeff_comp_support]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hz : matrixCoeff B k n = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.mpr h)
  rw [hz, mul_zero]

/-- **The trace is cyclic under a two-operator swap on a finite `Config`**, `Tr[AB] = Tr[BA]` —
the standard finite-dimensional matrix-trace cyclicity, from `matrixCoeff_comp` and swapping the
order of a double sum. **This is `[Fintype Config]`-specific finite-configuration infrastructure,
not a statistics-agnostic building block usable for both lines of Track D as-is**: the fermionic
`FermionOccupation Mode := Finset Mode` is a `Fintype` once `Mode` is, but the bosonic
`Occupation Mode := Mode →₀ ℕ` is genuinely infinite (unbounded occupation per mode) even for a
finite mode set, so it is *not* an instance of `[Fintype Config]` and this theorem does not apply
to it. A bosonic thermal-trace cyclicity needs a separate, summability-aware statement — e.g.
`Tr_w[AB] = Tr_w[BA]` for a `tsum`-convergent weighted trace, or the `ζ`-uniform Bloch–de Dominicis
induction
routed through a genuine KMS-type rotation identity rather than bare trace cyclicity — and is not
supplied here; see `notes/roadmaps/second-quantization.md`'s Phase 9 section. -/
theorem traceFock_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (A.comp B) = traceFock (B.comp A) := by
  simp only [traceFock, matrixCoeff_comp]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **`traceFock` is linear in its operator argument: scaling.** -/
theorem traceFock_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock (c • A) = c * traceFock A := by
  simp only [traceFock, matrixCoeff_smul, Finset.mul_sum]

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

/-- **`⟨0⟩_w = 0`**: the normalized weighted diagonal functional vanishes on the zero operator,
directly from `normalizedWeightedDiagonal_smul` at `c = 0`. -/
theorem normalizedWeightedDiagonal_zero (w : Config → ℂ) :
    normalizedWeightedDiagonal w (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
  have h := normalizedWeightedDiagonal_smul (0 : ℂ) w
    (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
  simpa using h

/-! ## Weighted traces of the identity -/

@[simp]
theorem traceFock_id : traceFock (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] _) =
    (Fintype.card Config : ℂ) := by
  have h : ∀ n : Config, matrixCoeff (LinearMap.id) n n = 1 := fun n =>
    matrixCoeff_of_smul_basisState (by rw [LinearMap.id_apply, one_smul])
  simp [traceFock, h]

/-- **The weighted trace of the identity is the total weight**,
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

/-! ## The `NormalizedOperatorFunctional` instantiation -/

/-- **The finite-sum instantiation** of `NormalizedOperatorFunctional`, for a weight `w : Config →
ℂ` with nonzero total weight: `toLinearMap := normalizedWeightedDiagonal w`, with linearity
supplied by `normalizedWeightedDiagonal_add`/`_smul` and normalization by
`normalizedWeightedDiagonal_id`. -/
noncomputable def normalizedWeightedDiagonalFunctional (w : Config → ℂ) (hw : weightSum w ≠ 0) :
    NormalizedOperatorFunctional Config where
  toLinearMap :=
    { toFun := normalizedWeightedDiagonal w
      map_add' := normalizedWeightedDiagonal_add w
      map_smul' := fun c A => normalizedWeightedDiagonal_smul c w A }
  map_id := normalizedWeightedDiagonal_id w hw

@[simp]
theorem normalizedWeightedDiagonalFunctional_apply (w : Config → ℂ) (hw : weightSum w ≠ 0)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    normalizedWeightedDiagonalFunctional w hw A = normalizedWeightedDiagonal w A := rfl

end Common
end SecondQuantization
