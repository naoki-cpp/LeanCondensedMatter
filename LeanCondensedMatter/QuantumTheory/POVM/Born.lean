import LeanCondensedMatter.Analysis.InfiniteSum.Fiberwise
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder
import LeanCondensedMatter.QuantumTheory.POVM.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option linter.style.header false

/-!
# Born probabilities for discrete POVMs

A Born probability is represented canonically as a nonnegative real number. The underlying complex
expectation is first proved self-adjoint and transported losslessly to `ℝ`; its nonnegativity then
bundles the value as `NNReal`. `bornPMF` packages all countable outcomes as a normalized probability
mass function.

Probability normalization follows from a nonnegative summable double series over density
eigenvectors and measurement outcomes. The internal kernel uses lossless diagonal expectations of
positive effects and never defines a physical scalar by discarding an imaginary part with `.re`.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : Type*} [Countable M]

/-- Strong normalization implies diagonal weak-operator normalization. -/
theorem POVM.hasSum_inner_apply (P : POVM H M) (x : H) :
    HasSum (fun m => (inner ℂ x (P.E m x) : ℂ)) (inner ℂ x x) :=
  (innerSL ℂ x).hasSum (P.hasSum_apply x)

/-- The self-adjoint complex scalar `Tr(ρ Eₘ)` representing a Born probability. -/
noncomputable def probSelfAdjoint
    (P : POVM H M) (ρ : DensityOperator H) (m : M) : selfAdjoint ℂ :=
  ⟨ρ.expectation (P.E m),
    ρ.expectation_isSelfAdjoint_of_isPositive (P.pos m)⟩

/-- The canonical nonnegative Born probability. The real value is obtained losslessly from the
proved-self-adjoint complex expectation, and positivity of the effect supplies the nonnegativity
proof required by `NNReal`. -/
noncomputable def probNNReal (P : POVM H M) (ρ : DensityOperator H) (m : M) : NNReal :=
  NNReal.mk
    (Complex.selfAdjointEquiv (probSelfAdjoint P ρ m))
    (by
      unfold probSelfAdjoint Complex.selfAdjointEquiv
      exact ρ.expectation_re_nonneg_of_isPositive (P.pos m))

/-- The complex density-state expectation of a POVM effect is exactly the complex embedding of the
canonical nonnegative Born probability. -/
@[simp]
theorem DensityOperator.expectation_effect_eq_probNNReal
    (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    ρ.expectation (P.E m) = ((probNNReal P ρ m : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [probNNReal, probSelfAdjoint, Complex.selfAdjointEquiv] using
      ρ.expectation_im_eq_zero_of_isPositive (P.pos m)

private noncomputable def probabilityKernel (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) : ℝ :=
  a.1.1 * diagonalExpectationValue (P.E m) (P.pos m).isSelfAdjoint
    (eigenvectorFamily ρ.spectralTraceClass.compact a)

private theorem probabilityKernel_nonneg (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) (m : M) :
    0 ≤ probabilityKernel P ρ a m :=
  mul_nonneg
    (eigenvalue_nonneg_of_isPositive ρ.pos.toLinearMap a)
    (diagonalExpectationValue_nonneg (P.E m) (P.pos m)
      (eigenvectorFamily ρ.spectralTraceClass.compact a))

private theorem hasSum_probabilityKernel_outcome (P : POVM H M)
    (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    HasSum (fun m => probabilityKernel P ρ a m) a.1.1 := by
  let e := eigenvectorFamily ρ.spectralTraceClass.compact a
  have hinner : HasSum (fun m => (inner ℂ e (P.E m e) : ℂ)) (inner ℂ e e) :=
    P.hasSum_inner_apply e
  have hcomplex : HasSum
      (fun m => ((diagonalExpectationValue (P.E m) (P.pos m).isSelfAdjoint e : ℝ) : ℂ))
      ((1 : ℝ) : ℂ) := by
    simpa [inner_self_eq_norm_sq_to_K, e, eigenvectorFamily_norm_eq_one ρ a] using
      HasSum.congr_fun hinner fun m =>
        coe_diagonalExpectationValue_right (P.E m) (P.pos m).isSelfAdjoint e
  have hreal :
      HasSum (fun m => diagonalExpectationValue (P.E m) (P.pos m).isSelfAdjoint e) 1 :=
    Complex.hasSum_ofReal.mp hcomplex
  simpa [probabilityKernel, e] using hreal.mul_left a.1.1

private theorem hasSum_probabilityKernel_eigenvector (P : POVM H M)
    (ρ : DensityOperator H) (m : M) :
    HasSum (fun a => probabilityKernel P ρ a m) (probNNReal P ρ m : ℝ) := by
  have hcomplex := (ρ.summable_expectation_term (P.E m)).hasSum
  rw [← ρ.expectation_apply (P.E m), ρ.expectation_effect_eq_probNNReal P m] at hcomplex
  have hcomplex' :
      HasSum (fun a : EigenvectorIndex ρ.op => ((probabilityKernel P ρ a m : ℝ) : ℂ))
        (((probNNReal P ρ m : ℝ) : ℂ)) :=
    HasSum.congr_fun hcomplex fun a => by
      rw [probabilityKernel, Complex.ofReal_mul, coe_diagonalExpectationValue_right]
  exact Complex.hasSum_ofReal.mp hcomplex'

/-- The canonical nonnegative Born probabilities have sum one. -/
theorem hasSum_probNNReal (P : POVM H M) (ρ : DensityOperator H) :
    HasSum (probNNReal P ρ) 1 := by
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
  have hcol : ∀ m, HasSum (fun a => g (a, m)) (probNNReal P ρ m : ℝ) := fun m => by
    simpa [g] using hasSum_probabilityKernel_eigenvector P ρ m
  obtain ⟨_, hprob, htot⟩ :=
    tsum_fiberwise_eq_of_summable hg_summable hrow hcol
  have htrace : (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 := by
    simpa [spectralTrace] using ρ.spectralTrace_op_eq_one
  have hreal : HasSum (fun m => (probNNReal P ρ m : ℝ)) 1 := by
    rw [← htot.symm.trans htrace]
    exact hprob.hasSum
  exact (NNReal.hasSum_coe).mp hreal

/-- The normalized countable Born distribution associated with a POVM and density state. -/
noncomputable def bornPMF (P : POVM H M) (ρ : DensityOperator H) : PMF M :=
  ⟨fun m => (probNNReal P ρ m : ENNReal),
    (ENNReal.hasSum_coe).mpr (hasSum_probNNReal P ρ)⟩

/-- Evaluation of the Born probability mass function recovers the canonical nonnegative
probability, embedded in `ENNReal`. -/
@[simp]
theorem bornPMF_apply (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    bornPMF P ρ m = (probNNReal P ρ m : ENNReal) :=
  rfl

/-- Every canonical discrete Born probability is at most one. -/
theorem probNNReal_le_one (P : POVM H M) (ρ : DensityOperator H) (m : M) :
    probNNReal P ρ m ≤ 1 := by
  have h : (probNNReal P ρ m : ENNReal) ≤ 1 := by
    simpa using PMF.coe_le_one (bornPMF P ρ) m
  exact_mod_cast h

end QuantumTheory
