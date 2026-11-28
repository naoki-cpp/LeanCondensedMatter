import LeanCondensedMatter.Analysis.Algebra.FinsuppCoordinates
import LeanCondensedMatter.Analysis.Algebra.FinsuppDiagonal
import LeanCondensedMatter.Analysis.Algebra.FinsuppSupportShift
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option linter.style.header false

/-!
# Diagonal series of free-module endomorphisms

Coordinate expansions, diagonal traces, their summability domains, and cyclicity,
with explicit summability assumptions and no Hilbert-space structure.
-/

namespace Finsupp

variable {R ι κ : Type*} [NormedField R]

/-- The coordinate expansion can be written as an infinite sum because the input has finite support. -/
theorem linearMap_apply_eq_tsum (A : (ι →₀ R) →ₗ[R] (κ →₀ R))
    (x : ι →₀ R) (m : κ) :
    A x m = ∑' k, A (Finsupp.single k 1) m * x k := by
  rw [linearMap_apply_eq_finsetSum_of_support_subset A x x.support (subset_refl _) m]
  exact ((hasSum_sum_of_ne_finset_zero (s := x.support)
    (fun k hk => by rw [Finsupp.notMem_support_iff.mp hk, mul_zero])).tsum_eq).symm

section Trace

variable {Config : Type*}

/-- **The summability-aware diagonal trace**, `Tr'[A] := Σ'ₙ ⟨n|A|n⟩`.

The definition is available for arbitrary `Config`, but useful algebraic properties require
explicit summability assumptions because Mathlib defines a non-summable `tsum` to be zero. -/
noncomputable def tsumTrace (A : (Config →₀ R) →ₗ[R] (Config →₀ R)) : R :=
  ∑' n, A (Finsupp.single n 1) n

/-- `tsumTrace` is additive when both diagonal families are summable. -/
theorem tsumTrace_add {A B : (Config →₀ R) →ₗ[R] (Config →₀ R)}
    (hA : Summable (fun n => A (Finsupp.single n 1) n)) (hB : Summable (fun n => B (Finsupp.single n 1) n)) :
    tsumTrace (A + B) = tsumTrace A + tsumTrace B := by
  simp only [tsumTrace, LinearMap.add_apply, Finsupp.add_apply]
  exact hA.tsum_add hB

/-- `tsumTrace` scales unconditionally. -/
theorem tsumTrace_smul (c : R) (A : (Config →₀ R) →ₗ[R] (Config →₀ R)) :
    tsumTrace (c • A) = c * tsumTrace A := by
  simp only [tsumTrace, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    tsum_mul_left]


/-- Endomorphisms whose diagonal trace after left multiplication by `B` is summable.
This is a partial trace domain, not a Hilbert-space trace-class or operator-domain claim. -/
noncomputable def summableDiagonalTraceDomain
    (B : (Config →₀ R) →ₗ[R] (Config →₀ R)) :
    Submodule R ((Config →₀ R) →ₗ[R] (Config →₀ R)) where
  carrier := {A | Summable (fun n => (B.comp A) (Finsupp.single n 1) n)}
  zero_mem' := by
    change Summable (fun n : Config =>
      (B.comp (0 : (Config →₀ R) →ₗ[R] (Config →₀ R))) (Finsupp.single n 1) n)
    simpa [LinearMap.comp_zero] using
      (summable_zero : Summable (fun _ : Config => (0 : R)))
  add_mem' := by
    intro A C hA hC
    change Summable (fun n => (B.comp (A + C)) (Finsupp.single n 1) n)
    have h := hA.add hC
    simpa only [LinearMap.comp_add, LinearMap.add_apply, Finsupp.add_apply] using h
  smul_mem' := by
    intro c A hA
    change Summable (fun n => (B.comp (c • A)) (Finsupp.single n 1) n)
    have h := hA.mul_left c
    simpa only [LinearMap.comp_smul, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul] using h

/-- Membership is precisely summability of the weighted diagonal series. -/
@[simp]
theorem mem_summableDiagonalTraceDomain_iff
    (B A : (Config →₀ R) →ₗ[R] (Config →₀ R)) :
    A ∈ summableDiagonalTraceDomain B ↔
      Summable (fun n => (B.comp A) (Finsupp.single n 1) n) :=
  Iff.rfl

/-- Trace ratio as a linear functional on its summability domain.
A nonzero, summable denominator is needed before interpreting this as a normalized state. -/
noncomputable def summableDiagonalTraceRatioLinear
    (B : (Config →₀ R) →ₗ[R] (Config →₀ R)) :
    summableDiagonalTraceDomain B →ₗ[R] R where
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

/-- Endomorphisms with nonzero grading shift belong to every diagonal-weighted trace domain:
the numerator vanishes term by term, regardless of the weight. -/
theorem summable_diagonalOperator_comp_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : (Config →₀ R) →ₗ[R] (Config →₀ R)} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → R) :
    Summable (fun n => ((Finsupp.diagonalOperator w).comp A) (Finsupp.single n 1) n) := by
  simpa only [LinearMap.comp_apply, Finsupp.diagonalOperator_apply,
    hA.diagonal_eq_zero hq, mul_zero] using
    (summable_zero : Summable (fun _ : Config => (0 : R)))

/-- Every diagonal weighting annihilates the trace of a endomorphism with nonzero grading shift. -/
theorem tsumTrace_diagonalOperator_comp_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : (Config →₀ R) →ₗ[R] (Config →₀ R)} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → R) :
    tsumTrace ((Finsupp.diagonalOperator w).comp A) = 0 := by
  unfold tsumTrace
  simp only [LinearMap.comp_apply, Finsupp.diagonalOperator_apply,
    hA.diagonal_eq_zero hq, mul_zero, tsum_zero]

/-- The ratio of diagonal traces vanishes for endomorphism with nonzero grading shifts even when
the denominator is zero.  Interpreting the ratio as normalized requires a separate nonzero denominator hypothesis. -/
theorem diagonalTraceRatio_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : (Config →₀ R) →ₗ[R] (Config →₀ R)} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → R) :
    tsumTrace ((Finsupp.diagonalOperator w).comp A) / tsumTrace (Finsupp.diagonalOperator w) = 0 := by
  rw [tsumTrace_diagonalOperator_comp_eq_zero_of_carriesShift hA hq w]
  simp

/-- The common partial trace-ratio functional vanishes on endomorphism with nonzero grading shifts.
The summability witness is supplied automatically by the selection rule. -/
theorem summableDiagonalTraceRatioLinear_eq_zero_of_carriesShift
    {G : Type*} [AddCommGroup G] {grading : Config → G}
    {A : (Config →₀ R) →ₗ[R] (Config →₀ R)} {q : G}
    (hA : Finsupp.CarriesShift grading A q) (hq : q ≠ 0) (w : Config → R) :
    summableDiagonalTraceRatioLinear (Finsupp.diagonalOperator w)
      ⟨A, summable_diagonalOperator_comp_of_carriesShift hA hq w⟩ = 0 := by
  change tsumTrace ((Finsupp.diagonalOperator w).comp A) / tsumTrace (Finsupp.diagonalOperator w) = 0
  exact diagonalTraceRatio_eq_zero_of_carriesShift hA hq w


end Trace

variable [CompleteSpace R]

/-- The diagonal series of a composite is invariant under swapping the two factors
when the double series is summable. -/
theorem tsum_diagonal_comp_comm (A B : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (h : Summable (Function.uncurry
      (fun n k => A (Finsupp.single k 1) n * B (Finsupp.single n 1) k))) :
    tsumTrace (A.comp B) = tsumTrace (B.comp A) := by
  unfold tsumTrace
  calc
    _ = ∑' n, ∑' k, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
      tsum_congr fun n => linearMap_apply_eq_tsum A (B (Finsupp.single n 1)) n
    _ = ∑' k, ∑' n, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
      h.tsum_comm.symm
    _ = _ := tsum_congr fun k => by
      change _ = B (A (Finsupp.single k 1)) k
      rw [linearMap_apply_eq_tsum]
      exact tsum_congr fun n => mul_comm _ _

/-- Summability of the double series implies summability of the composite's diagonal. -/
theorem summable_diagonal_comp_of_summable_uncurry
    (A B : (ι →₀ R) →ₗ[R] (ι →₀ R))
    (h : Summable (Function.uncurry
      (fun n k => A (Finsupp.single k 1) n * B (Finsupp.single n 1) k))) :
    Summable (fun n => (A.comp B) (Finsupp.single n 1) n) := by
  have hrow : (fun n => (A.comp B) (Finsupp.single n 1) n) =
      fun n => ∑' k, A (Finsupp.single k 1) n * B (Finsupp.single n 1) k :=
    funext fun n => linearMap_apply_eq_tsum A (B (Finsupp.single n 1)) n
  rw [hrow]
  exact h.prod

end Finsupp
