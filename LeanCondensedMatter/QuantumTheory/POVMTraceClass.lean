import LeanCondensedMatter.Analysis.InfiniteSum.Fiberwise
import LeanCondensedMatter.QuantumTheory.DensityOperatorExpectationOrder
import Mathlib.LinearAlgebra.Complex.Module

set_option linter.style.header false

/-!
# Discrete POVMs for trace-class density states

This module equips the canonical `QuantumTheory.TraceClass.POVM` type with the Born probability API
for arbitrary countable discrete outcome types. The normalization is stated in the strong operator
topology:

`∀ x, HasSum (fun m => E m x) x`.

The Born scalar is first represented as a self-adjoint complex number and then transported, without
loss of information, to `ℝ` through `Complex.selfAdjointEquiv`. Probability normalization follows
from an explicitly nonnegative, summable double-series argument over density eigenvectors and
measurement outcomes.

General measurable POVMs, continuous outcomes, and unbounded observables remain outside this
bounded discrete interface.
-/

noncomputable section

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : Type*} [Countable M]

/-- Strong normalization implies the corresponding diagonal weak-operator normalization. -/
theorem POVM.hasSum_inner_apply (P : POVM H M) (x : H) :
    HasSum (fun m => (inner ℂ x (P.E m x) : ℂ)) (inner ℂ x x) := by
  exact (innerSL ℂ x).hasSum (P.hasSum_apply x)

/-- The self-adjoint complex scalar `Tr(ρ Eₘ)` representing one Born probability. -/
noncomputable def probSelfAdjoint
    (P : POVM H M) (ρ : DensityOperator H) (m : M) : selfAdjoint ℂ :=
  ⟨ρ.expectation (P.E m),
    ρ.expectation_isSelfAdjoint_of_isPositive (P.pos m)⟩

/-- The real Born probability obtained losslessly from the self-adjoint scalar `Tr(ρ Eₘ)`. -/
noncomputable def prob (P : POVM H M) (ρ : DensityOperator H) (m : M) : ℝ :=
  Complex.selfAdjointEquiv (probSelfAdjoint P ρ m)

/-- Every discrete Born probability is nonnegative. -/
theorem prob_nonneg (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    0 ≤ prob P ρ m := by
  unfold prob probSelfAdjoint Complex.selfAdjointEquiv
  exact ρ.expectation_re_nonneg_of_isPositive (P.pos m)

private noncomputable def probabilityKernel (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) : ℝ :=
  a.1.1 *
    (inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
      (P.E m (eigenvectorFamily ρ.spectralTraceClass.compact a)) : ℂ).re

private theorem probabilityKernel_nonneg (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) :
    0 ≤ probabilityKernel P ρ a m := by
  exact mul_nonneg
    (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)
    ((P.pos m).re_inner_nonneg_right
      (eigenvectorFamily ρ.spectralTraceClass.compact a))

private theorem hasSum_probabilityKernel_outcome (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    HasSum (fun m => probabilityKernel P ρ a m) a.1.1 := by
  let e := eigenvectorFamily ρ.spectralTraceClass.compact a
  have hinner : HasSum (fun m => (inner ℂ e (P.E m e) : ℂ)) (inner ℂ e e) :=
    P.hasSum_inner_apply e
  have hre : HasSum (fun m => (inner ℂ e (P.E m e) : ℂ).re) 1 := by
    have h := Complex.reCLM.hasSum hinner
    simpa [inner_self_eq_norm_sq_to_K, e, eigenvectorFamily_norm_eq_one ρ a] using h
  simpa [probabilityKernel, e] using hre.mul_left a.1.1

private theorem hasSum_probabilityKernel_eigenvector (P : POVM H M)
    (ρ : DensityOperator H) (m : M) :
    HasSum (fun a => probabilityKernel P ρ a m) (prob P ρ m) := by
  have h := Complex.reCLM.hasSum (ρ.summable_expectation_term (P.E m)).hasSum
  simpa [prob, probSelfAdjoint, probabilityKernel, DensityOperator.expectation_apply,
    Complex.mul_re] using h

/-- The countable family of Born probabilities is summable and normalized. -/
theorem summable_prob_and_tsum_eq_one (P : POVM H M) (ρ : DensityOperator H) :
    Summable (prob P ρ) ∧ ∑' m, prob P ρ m = 1 := by
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
  have hcol : ∀ m, HasSum (fun a => g (a, m)) (prob P ρ m) := fun m => by
    simpa [g] using hasSum_probabilityKernel_eigenvector P ρ m
  obtain ⟨_, hprob, htot⟩ :=
    tsum_fiberwise_eq_of_summable hg_summable hrow hcol
  have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
    simpa [SpectralTraceClass.trace, spectralTrace] using ρ.spectralTrace_eq_one
  exact ⟨hprob, htot.symm.trans htrace⟩

/-- Discrete Born probabilities are summable. -/
theorem summable_prob (P : POVM H M) (ρ : DensityOperator H) :
    Summable (prob P ρ) :=
  (summable_prob_and_tsum_eq_one P ρ).1

/-- The countable sum of all Born probabilities is one. -/
theorem tsum_prob_eq_one (P : POVM H M) (ρ : DensityOperator H) :
    ∑' m, prob P ρ m = 1 :=
  (summable_prob_and_tsum_eq_one P ρ).2

/-- Every discrete Born probability is at most one. -/
theorem prob_le_one (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    prob P ρ m ≤ 1 := by
  calc
    prob P ρ m = ∑ i ∈ ({m} : Finset M), prob P ρ i := by simp
    _ ≤ ∑' i, prob P ρ i :=
      (summable_prob P ρ).sum_le_tsum {m} (fun i _ => prob_nonneg P ρ i)
    _ = 1 := tsum_prob_eq_one P ρ

section FiniteOutcomes

variable {M : Type*} [Fintype M]

/-- For finite outcome types, countable normalization reduces to the ordinary finite sum. -/
theorem sum_prob_eq_one (P : POVM H M) (ρ : DensityOperator H) :
    ∑ m, prob P ρ m = 1 := by
  simpa using tsum_prob_eq_one P ρ

end FiniteOutcomes

end QuantumTheory.TraceClass
