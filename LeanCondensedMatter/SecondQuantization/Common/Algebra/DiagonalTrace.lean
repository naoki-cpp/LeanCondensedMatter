import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Matrix coefficients and summability-aware diagonal traces

Statistics-independent matrix-coefficient and diagonal-trace infrastructure on
`AlgebraicFock Config`. The extensionality and support formulas hold for arbitrary configuration
types. The `tsum` trace API is therefore usable for genuinely infinite configuration spaces,
provided callers carry the required summability hypotheses explicitly.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-! ## Matrix coefficients -/

/-- **Diagonal matrix coefficients.** If `A` acts on `basisState n` as `c • basisState n`, the
`(n, n)` matrix coefficient is exactly `c`. -/
theorem matrixCoeff_of_smul_basisState {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    {n : Config} {c : ℂ} (h : A (basisState n) = c • basisState n) :
    matrixCoeff A n n = c := by
  change A (basisState n) n = c
  rw [h, smul_basisState_apply_self]

/-- **Two operators agreeing on every matrix coefficient are equal.** -/
theorem matrixCoeff_ext {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (h : ∀ m n, matrixCoeff A m n = matrixCoeff B m n) : A = B := by
  apply linearMap_ext_basisState
  intro n
  apply Finsupp.ext
  intro m
  exact h m n

/-! ## Composition of matrix coefficients -/

/-- **`matrixCoeff` under composition, as a sum over `B`'s finite support**:
`(AB)_{mn} = Σ_{k ∈ supp(B|n⟩)} A_{mk} B_{kn}`. This holds for arbitrary `Config`, because an
`AlgebraicFock Config` vector is finitely supported even when `Config` itself is infinite. -/
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

/-- **`matrixCoeff` under composition is ordinary matrix multiplication** on a finite
configuration type: `(AB)_{mn} = Σₖ A_{mk} B_{kn}`. -/
theorem matrixCoeff_comp [Fintype Config]
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑ k : Config, matrixCoeff A m k * matrixCoeff B k n := by
  rw [matrixCoeff_comp_support]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hz : matrixCoeff B k n = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.mpr h)
  rw [hz, mul_zero]

/-! ## The `tsum` diagonal trace -/

/-- **The summability-aware diagonal trace**, `Tr'[A] := Σ'ₙ ⟨n|A|n⟩`.

The definition is available for arbitrary `Config`, but useful algebraic properties require
explicit summability assumptions because Mathlib defines a non-summable `tsum` to be zero. -/
noncomputable def tsumTrace (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  ∑' n, matrixCoeff A n n

/-- `tsumTrace` is additive when both diagonal families are summable. -/
theorem tsumTrace_add {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config}
    (hA : Summable (fun n => matrixCoeff A n n)) (hB : Summable (fun n => matrixCoeff B n n)) :
    tsumTrace (A + B) = tsumTrace A + tsumTrace B := by
  rw [tsumTrace, tsumTrace, tsumTrace, ← (hA.hasSum.add hB.hasSum).tsum_eq]
  exact tsum_congr fun n => matrixCoeff_add A B n n

/-- `tsumTrace` scales unconditionally. -/
theorem tsumTrace_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    tsumTrace (c • A) = c * tsumTrace A := by
  rw [tsumTrace, tsumTrace]
  simp_rw [matrixCoeff_smul]
  exact tsum_mul_left

/-- **Cyclicity under a two-operator swap**, assuming absolute double summability:
`Tr'[AB] = Tr'[BA]`. -/
theorem tsumTrace_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    tsumTrace (A.comp B) = tsumTrace (B.comp A) := by
  rw [tsumTrace, tsumTrace]
  have hrow : ∀ n, (∑' k, matrixCoeff A n k * matrixCoeff B k n) = matrixCoeff (A.comp B) n n := by
    intro n
    rw [matrixCoeff_comp_support]
    exact (hasSum_sum_of_ne_finset_zero
      (s := (B (basisState n)).support)
      (fun k hk => by
        have hz : matrixCoeff B k n = 0 := by
          by_contra hcon
          exact hk (Finsupp.mem_support_iff.mpr hcon)
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
          by_contra hcon
          exact hn (Finsupp.mem_support_iff.mpr hcon)
        rw [hz, mul_zero])).tsum_eq
  calc
    ∑' n, matrixCoeff (A.comp B) n n
        = ∑' n, ∑' k, matrixCoeff A n k * matrixCoeff B k n :=
          tsum_congr fun n => (hrow n).symm
    _ = ∑' k, ∑' n, matrixCoeff A n k * matrixCoeff B k n := h.tsum_comm.symm
    _ = ∑' n, matrixCoeff (B.comp A) n n := tsum_congr fun k => hcol k

/-- A composite's diagonal series is summable whenever the underlying bivariate family is. -/
theorem summable_matrixCoeff_diag_comp_of_summable_uncurry
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    Summable (fun n => matrixCoeff (A.comp B) n n) := by
  have hrow : (fun n => matrixCoeff (A.comp B) n n) =
      fun n => ∑' k, matrixCoeff A n k * matrixCoeff B k n := by
    funext n
    rw [matrixCoeff_comp_support]
    exact ((hasSum_sum_of_ne_finset_zero
      (s := (B (basisState n)).support)
      (fun k hk => by
        have hz : matrixCoeff B k n = 0 := by
          by_contra hcon
          exact hk (Finsupp.mem_support_iff.mpr hcon)
        rw [hz, mul_zero])).tsum_eq).symm
  rw [hrow]
  exact h.prod

end Common
end SecondQuantization
