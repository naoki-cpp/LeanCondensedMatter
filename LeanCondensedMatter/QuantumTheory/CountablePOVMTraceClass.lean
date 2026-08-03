import LeanCondensedMatter.Analysis.InfiniteSum.Fiberwise
import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationOrder
import Mathlib.LinearAlgebra.Complex.Module

set_option linter.style.header false

/-!
# Countable discrete POVMs for trace-class density states

This module extends the finite-outcome `QuantumTheory.TraceClass.POVM` API to countable discrete
outcome types. The normalization is stated in the strong operator topology:

`∀ x, HasSum (fun m => E m x) x`.

This is weaker than operator-norm summability and is the natural convergence notion for countable
families of positive measurement effects. The Born probability is first represented as a
self-adjoint complex scalar and then transported, without loss of information, to `ℝ` through
`Complex.selfAdjointEquiv`. Its normalization is proved by an explicitly summable, nonnegative
double-series argument over density eigenvectors and measurement outcomes.

General measurable POVMs and unbounded observables remain outside this discrete bounded-operator
interface.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : Type*} [Countable M]

/-- A countable discrete POVM whose positive effects sum strongly to the identity. -/
structure CountablePOVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : Type*) [Countable M] where
  /-- The bounded positive effect associated with an outcome. -/
  E : M → H →L[ℂ] H
  /-- Every effect is positive. -/
  pos : ∀ m, (E m).IsPositive
  /-- Strong-operator normalization: the effect family sums pointwise to the identity. -/
  hasSum_apply : ∀ x, HasSum (fun m => E m x) x

namespace CountablePOVM

/-- Strong normalization implies the corresponding diagonal weak-operator normalization. -/
theorem hasSum_inner_apply (P : CountablePOVM H M) (x : H) :
    HasSum (fun m => (inner ℂ x (P.E m x) : ℂ)) (inner ℂ x x) := by
  exact (innerSL ℂ x).hasSum (P.hasSum_apply x)

/-- The self-adjoint complex scalar `Tr(ρ Eₘ)` representing one Born probability. -/
noncomputable def probSelfAdjoint
    (P : CountablePOVM H M) (ρ : DensityOperator H) (m : M) : selfAdjoint ℂ :=
  ⟨ρ.expectation (P.E m),
    ρ.expectation_isSelfAdjoint_of_isPositive (P.pos m)⟩

/-- The real Born probability obtained losslessly from the self-adjoint scalar `Tr(ρ Eₘ)`. -/
noncomputable def prob (P : CountablePOVM H M) (ρ : DensityOperator H) (m : M) : ℝ :=
  Complex.selfAdjointEquiv (P.probSelfAdjoint ρ m)

/-- Every countable-discrete Born probability is nonnegative. -/
theorem prob_nonneg (P : CountablePOVM H M) (ρ : DensityOperator H) (m : M) :
    0 ≤ P.prob ρ m := by
  change 0 ≤ (ρ.expectation (P.E m)).re
  exact ρ.expectation_re_nonneg_of_isPositive (P.pos m)

private noncomputable def probabilityKernel (P : CountablePOVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) : ℝ :=
  a.1.1 *
    (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
      (P.E m (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ).re

private theorem probabilityKernel_nonneg (P : CountablePOVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) :
    0 ≤ probabilityKernel P ρ a m := by
  exact mul_nonneg
    (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)
    ((P.pos m).re_inner_nonneg_right
      (eigenvectorFamily ρ.spectralTraceClass.compact a))

private theorem hasSum_probabilityKernel_outcome (P : CountablePOVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    HasSum (fun m => probabilityKernel P ρ a m) a.1.1 := by
  let e := eigenvectorFamily ρ.spectralTraceClass.compact a
  have hinner : HasSum (fun m => (inner ℂ e (P.E m e) : ℂ)) (inner ℂ e e) :=
    P.hasSum_inner_apply e
  have hre : HasSum (fun m => (inner ℂ e (P.E m e) : ℂ).re) 1 := by
    have h := Complex.reCLM.hasSum hinner
    simpa [inner_self_eq_norm_sq_to_K, e, eigenvectorFamily_norm_eq_one ρ a] using h
  simpa [probabilityKernel, e] using hre.mul_left a.1.1

private theorem hasSum_probabilityKernel_eigenvector (P : CountablePOVM H M)
    (ρ : DensityOperator H) (m : M) :
    HasSum (fun a => probabilityKernel P ρ a m) (P.prob ρ m) := by
  change HasSum (fun a => probabilityKernel P ρ a m) (ρ.expectation (P.E m)).re
  have h := Complex.reCLM.hasSum (ρ.summable_expectation_term (P.E m)).hasSum
  simpa [probabilityKernel, DensityOperator.expectation_apply, Complex.mul_re] using h

/-- The countable family of Born probabilities is summable and normalized. -/
theorem summable_prob_and_tsum_eq_one (P : CountablePOVM H M) (ρ : DensityOperator H) :
    Summable (P.prob ρ) ∧ ∑' m, P.prob ρ m = 1 := by
  let g : EigenvectorIndex ρ.op × M → ℝ :=
    fun p => probabilityKernel P ρ p.1 p.2
  have hg_nonneg : ∀ p, 0 ≤ g p := fun p =>
    probabilityKernel_nonneg P ρ p.1 p.2
  have hrow : ∀ a, HasSum (fun m => g (a, m)) a.1.1 := fun a => by
    simpa [g] using hasSum_probabilityKernel_outcome P ρ a
  have hg_summable : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).mpr ⟨fun a => (hrow a).summable, by
      simpa only [fun a => (hrow a).tsum_eq] using
        summable_eigenvectorIndex ρ.spectralTraceClass.summable⟩
  have hcol : ∀ m, HasSum (fun a => g (a, m)) (P.prob ρ m) := fun m => by
    simpa [g] using hasSum_probabilityKernel_eigenvector P ρ m
  obtain ⟨_, hprob, htot⟩ :=
    tsum_fiberwise_eq_of_summable hg_summable hrow hcol
  have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
    simpa [SpectralTraceClass.trace, spectralTrace] using ρ.spectralTrace_eq_one
  exact ⟨hprob, htot.symm.trans htrace⟩

/-- Countable-discrete Born probabilities are summable. -/
theorem summable_prob (P : CountablePOVM H M) (ρ : DensityOperator H) :
    Summable (P.prob ρ) :=
  (P.summable_prob_and_tsum_eq_one ρ).1

/-- The countable sum of all Born probabilities is one. -/
theorem tsum_prob_eq_one (P : CountablePOVM H M) (ρ : DensityOperator H) :
    ∑' m, P.prob ρ m = 1 :=
  (P.summable_prob_and_tsum_eq_one ρ).2

/-- Every countable-discrete Born probability is at most one. -/
theorem prob_le_one (P : CountablePOVM H M) (ρ : DensityOperator H) (m : M) :
    P.prob ρ m ≤ 1 := by
  calc
    P.prob ρ m = ∑ i ∈ ({m} : Finset M), P.prob ρ i := by simp
    _ ≤ ∑' i, P.prob ρ i :=
      (P.summable_prob ρ).sum_le_tsum {m} (fun i _ => P.prob_nonneg ρ i)
    _ = 1 := P.tsum_prob_eq_one ρ

end CountablePOVM

section FiniteCompatibility

variable {M : Type*} [Fintype M]

/-- Every finite POVM determines a countable-discrete POVM by finite strong summation. -/
noncomputable def POVM.toCountable (P : POVM H M) : CountablePOVM H M where
  E := P.E
  pos := P.pos
  hasSum_apply := by
    intro x
    have hs : HasSum (fun m => P.E m x) (∑ m, P.E m x) := hasSum_fintype _
    have hsum : ∑ m, P.E m x = x := by
      have h := map_sum (ContinuousLinearMap.apply ℂ H x) P.E Finset.univ
      simp only [ContinuousLinearMap.apply_apply] at h
      rw [← h, P.sum_eq_id, ContinuousLinearMap.id_apply]
    rwa [hsum] at hs

/-- The countable and finite Born-probability definitions agree on a finite POVM. -/
@[simp]
theorem POVM.toCountable_prob (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    P.toCountable.prob ρ m = prob P ρ m := by
  change (ρ.expectation (P.E m)).re = prob P ρ m
  rw [ρ.expectation_apply]
  rfl

end FiniteCompatibility

end QuantumTheory.TraceClass
