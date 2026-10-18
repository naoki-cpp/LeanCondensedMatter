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
  simp only [tsumTrace, ← matrixCoeffLinear_apply, map_add]
  exact hA.tsum_add hB

/-- `tsumTrace` scales unconditionally. -/
theorem tsumTrace_smul (c : ℂ) (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    tsumTrace (c • A) = c * tsumTrace A := by
  simp only [tsumTrace, ← matrixCoeffLinear_apply, map_smul, smul_eq_mul,
    tsum_mul_left]

/-- Sum the matrix coefficients of a composite over the finite support of its right factor. -/
private theorem matrixCoeff_comp_eq_tsum
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (m n : Config) :
    matrixCoeff (A.comp B) m n = ∑' k, matrixCoeff A m k * matrixCoeff B k n := by
  rw [matrixCoeff_comp_support]
  exact ((hasSum_sum_of_ne_finset_zero
    (s := (B (basisState n)).support)
    (fun k hk => by
      have hz : matrixCoeff B k n = 0 := by
        by_contra hcon
        exact hk (Finsupp.mem_support_iff.mpr hcon)
      rw [hz, mul_zero])).tsum_eq).symm

/-- **Cyclicity under a two-operator swap**, assuming absolute double summability:
`Tr'[AB] = Tr'[BA]`. -/
theorem tsumTrace_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    tsumTrace (A.comp B) = tsumTrace (B.comp A) := by
  rw [tsumTrace, tsumTrace]
  calc
    ∑' n, matrixCoeff (A.comp B) n n
        = ∑' n, ∑' k, matrixCoeff A n k * matrixCoeff B k n :=
          tsum_congr fun n => matrixCoeff_comp_eq_tsum A B n n
    _ = ∑' k, ∑' n, matrixCoeff A n k * matrixCoeff B k n := h.tsum_comm.symm
    _ = ∑' n, matrixCoeff (B.comp A) n n := tsum_congr fun k => by
      rw [matrixCoeff_comp_eq_tsum]
      exact tsum_congr fun n => mul_comm _ _

/-- A composite's diagonal series is summable whenever the underlying bivariate family is. -/
theorem summable_matrixCoeff_diag_comp_of_summable_uncurry
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    Summable (fun n => matrixCoeff (A.comp B) n n) := by
  have hrow : (fun n => matrixCoeff (A.comp B) n n) =
      fun n => ∑' k, matrixCoeff A n k * matrixCoeff B k n :=
    funext fun n => matrixCoeff_comp_eq_tsum A B n n
  rw [hrow]
  exact h.prod

end Common
end SecondQuantization
