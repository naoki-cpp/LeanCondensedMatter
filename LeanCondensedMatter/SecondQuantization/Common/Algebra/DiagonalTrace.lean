import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# Summability-aware diagonal traces

The matrix-coefficient algebra is owned upstream by `AlgebraicFock`. This file contains the
statistics-independent diagonal `tsum` trace on `AlgebraicFock Config`. The definition is available
for arbitrary configuration types; useful algebraic properties carry explicit summability
hypotheses because Mathlib defines a non-summable `tsum` to be zero.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

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
  exact tsum_congr fun n => by
    simpa only [matrixCoeffLinear_apply] using (matrixCoeffLinear n n).map_add A B

/-- `tsumTrace` scales unconditionally. -/
theorem tsumTrace_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    tsumTrace (c • A) = c * tsumTrace A := by
  rw [tsumTrace, tsumTrace]
  have hpoint : (fun n => matrixCoeff (c • A) n n) =
      fun n => c * matrixCoeff A n n := by
    funext n
    simpa only [matrixCoeffLinear_apply, smul_eq_mul] using
      (matrixCoeffLinear n n).map_smul c A
  rw [hpoint]
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
