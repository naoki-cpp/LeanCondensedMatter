import LeanCondensedMatter.Analysis.Algebra.FinsuppTrace
import LeanCondensedMatter.Analysis.Algebra.FinsuppDiagonal
import LeanCondensedMatter.Analysis.Algebra.FinsuppSupportShift
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


/-- Algebraic observables whose diagonal trace after left multiplication by `B` is summable.
This is a partial trace domain, not a Hilbert-space trace-class or operator-domain claim. -/
noncomputable def summableDiagonalTraceDomain
    (B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    Submodule ℂ (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) where
  carrier := {A | Summable (fun n => matrixCoeff (B.comp A) n n)}
  zero_mem' := by
    change Summable (fun n : Config =>
      matrixCoeff (B.comp (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) n n)
    simpa [LinearMap.comp_zero, matrixCoeff] using
      (summable_zero : Summable (fun _ : Config => (0 : ℂ)))
  add_mem' := by
    intro A C hA hC
    change Summable (fun n => matrixCoeff (B.comp (A + C)) n n)
    have h := hA.add hC
    simpa only [LinearMap.comp_add, ← matrixCoeffLinear_apply, map_add] using h
  smul_mem' := by
    intro c A hA
    change Summable (fun n => matrixCoeff (B.comp (c • A)) n n)
    have h := hA.mul_left c
    simpa only [LinearMap.comp_smul, ← matrixCoeffLinear_apply, map_smul, smul_eq_mul] using h

/-- Membership is precisely summability of the weighted diagonal series. -/
@[simp]
theorem mem_summableDiagonalTraceDomain_iff
    (B A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    A ∈ summableDiagonalTraceDomain B ↔
      Summable (fun n => matrixCoeff (B.comp A) n n) :=
  Iff.rfl

/-- Trace ratio as a linear functional on its summability domain.
A nonzero, summable denominator is needed before interpreting this as a normalized state. -/
noncomputable def summableDiagonalTraceRatioLinear
    (B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    summableDiagonalTraceDomain B →ₗ[ℂ] ℂ where
  toFun := fun A => tsumTrace (B.comp A.1) / tsumTrace B
  map_add' := by
    intro A C
    change tsumTrace (B.comp (A.1 + C.1)) / tsumTrace B =
      tsumTrace (B.comp A.1) / tsumTrace B +
        tsumTrace (B.comp C.1) / tsumTrace B
    rw [LinearMap.comp_add, tsumTrace_add A.2 C.2, add_div]
  map_smul' := by
    intro c A
    change tsumTrace (B.comp (c • A.1)) / tsumTrace B =
      c * (tsumTrace (B.comp A.1) / tsumTrace B)
    rw [LinearMap.comp_smul, tsumTrace_smul, mul_div_assoc]


/-! ## Selection rules for diagonal traces -/

/-- A nonzero grading shift remains off-diagonal after multiplication by any diagonal
weight.  No positivity, trace-class condition, or countability hypothesis is needed. -/
theorem matrixCoeff_diagonalOperator_comp_self_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0)
    (w : Config → ℂ) (n : Config) :
    matrixCoeff ((Finsupp.diagonalOperator w).comp A) n n = 0 := by
  have hdiag : matrixCoeff A n n = 0 :=
    hA.diagonal_eq_zero hq n
  calc
    matrixCoeff ((Finsupp.diagonalOperator w).comp A) n n =
        w n * matrixCoeff A n n := by
          simp only [matrixCoeff, LinearMap.comp_apply, Finsupp.diagonalOperator_apply]
    _ = 0 := by rw [hdiag, mul_zero]

/-- Nonzero-charge observables belong to every diagonal-weighted trace domain:
the numerator vanishes term by term, regardless of the weight. -/
theorem summable_diagonalOperator_comp_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → ℂ) :
    Summable (fun n => matrixCoeff ((Finsupp.diagonalOperator w).comp A) n n) := by
  have hzero : (fun n => matrixCoeff ((Finsupp.diagonalOperator w).comp A) n n) =
      (fun _ : Config => (0 : ℂ)) := by
    funext n
    exact matrixCoeff_diagonalOperator_comp_self_eq_zero_of_carriesShift hA hq w n
  rw [hzero]
  exact summable_zero

/-- Every diagonal weighting annihilates the trace of a nonzero-charge observable. -/
theorem tsumTrace_diagonalOperator_comp_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → ℂ) :
    tsumTrace ((Finsupp.diagonalOperator w).comp A) = 0 := by
  unfold tsumTrace
  simp only [matrixCoeff_diagonalOperator_comp_self_eq_zero_of_carriesShift hA hq w,
    tsum_zero]

/-- The ratio of diagonal traces vanishes for nonzero-charge observables even when
the denominator is zero.  Physical state normalization still requires a separate
nonzero partition function hypothesis. -/
theorem diagonalTraceRatio_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → ℂ) :
    tsumTrace ((Finsupp.diagonalOperator w).comp A) / tsumTrace (Finsupp.diagonalOperator w) = 0 := by
  rw [tsumTrace_diagonalOperator_comp_eq_zero_of_carriesShift hA hq w]
  simp

/-- The common partial trace-ratio functional vanishes on nonzero-charge observables.
The summability witness is supplied automatically by the selection rule. -/
theorem summableDiagonalTraceRatioLinear_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → ℂ) :
    summableDiagonalTraceRatioLinear (Finsupp.diagonalOperator w)
      ⟨A, summable_diagonalOperator_comp_of_carriesShift hA hq w⟩ = 0 := by
  change tsumTrace ((Finsupp.diagonalOperator w).comp A) / tsumTrace (Finsupp.diagonalOperator w) = 0
  exact diagonalTraceRatio_eq_zero_of_carriesShift hA hq w

/-- Cyclicity of the Fock diagonal trace under absolute double summability. -/
theorem tsumTrace_comp_comm (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    tsumTrace (A.comp B) = tsumTrace (B.comp A) :=
  Finsupp.tsum_diagonal_comp_comm A B h

/-- A composite's diagonal series is summable whenever the underlying bivariate family is. -/
theorem summable_matrixCoeff_diag_comp_of_summable_uncurry
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (h : Summable (Function.uncurry (fun n k => matrixCoeff A n k * matrixCoeff B k n))) :
    Summable (fun n => matrixCoeff (A.comp B) n n) :=
  Finsupp.summable_diagonal_comp_of_summable_uncurry A B h

end Common
end SecondQuantization
