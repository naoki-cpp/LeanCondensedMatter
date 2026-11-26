import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral
import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.Analysis.FunctionalCalculus.CFC
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Von Neumann entropy

The canonical entropy is `ENNReal`-valued because a density operator can have infinite entropy even
when it is trace-class. The bounded entropy operator `-ρ log ρ` is also provided; using its finite
trace requires the additional hypothesis that this entropy operator is trace-class.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded entropy operator obtained by applying `x ↦ -x log x` to a density operator. -/
noncomputable def entropyOp (ρ : DensityOperator H) : H →L[ℂ] H :=
  cfc Real.negMulLog ρ.op

/-- The entropy operator acts on an eigenvector by applying `Real.negMulLog` to its eigenvalue. -/
theorem entropyOp_apply_eigenvector (ρ : DensityOperator H) {v : H} {c : ℝ}
    (hv : (ρ.op : H →ₗ[ℂ] H) v = (c : ℂ) • v) :
    entropyOp ρ v = (Real.negMulLog c : ℂ) • v := by
  simpa [entropyOp] using
    (cfc_apply_eigenvector (T := ρ.op) ρ.pos.isSelfAdjoint hv
      (f := Real.negMulLog) Real.continuous_negMulLog)

/-- The entropy operator of a density operator is compact. -/
theorem entropyOp_isCompact (ρ : DensityOperator H) :
    IsCompactOperator (entropyOp ρ : H →L[ℂ] H) := by
  rw [entropyOp]
  exact isCompactOperator_cfc_of_zero ρ.pos.isSelfAdjoint ρ.isTraceClass.isCompact
    Real.continuous_negMulLog (by simp)

/-- The entropy operator is self-adjoint. -/
theorem entropyOp_isSelfAdjoint (ρ : DensityOperator H) :
    IsSelfAdjoint (entropyOp ρ) := by
  rw [entropyOp]
  exact cfc_predicate _ _

/-- The transformed eigenvalues sum to the lossless real trace of the entropy operator. -/
theorem hasSum_negMulLog_eigenvalues (ρ : DensityOperator H)
    (htrace : IsTraceClass (entropyOp ρ)) :
    HasSum (fun a : EigenvectorIndex ρ.op => Real.negMulLog a.1.1)
      (htrace.realTrace (entropyOp_isSelfAdjoint ρ)) := by
  obtain ⟨u, b, hb⟩ := exists_diagonal_hilbertBasis_hasSum_iff
    ρ.isTraceClass.isCompact ρ.isSelfAdjoint (entropyOp_isSelfAdjoint ρ)
    Real.negMulLog (by simp) (fun _ _ hv => entropyOp_apply_eigenvector ρ hv)
  exact (hb _).mp (htrace.hasSum_realTrace (entropyOp_isSelfAdjoint ρ) b)

/-- The von Neumann entropy of a density operator, allowing the value `∞`. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ENNReal :=
  ∑' a : EigenvectorIndex ρ.op, ENNReal.ofReal (Real.negMulLog a.1.1)

/-- Entropy is finite with real value the entropy `tsum` whenever that sum converges. -/
theorem vonNeumannEntropy_ne_top_and_toReal_eq_tsum (ρ : DensityOperator H)
    (hsum : Summable (fun a : EigenvectorIndex ρ.op => Real.negMulLog a.1.1)) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      (vonNeumannEntropy ρ).toReal = ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 := by
  have hnonneg : ∀ a : EigenvectorIndex ρ.op, 0 ≤ Real.negMulLog a.1.1 :=
    fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a)
  have hEntropyEq : vonNeumannEntropy ρ =
      ENNReal.ofReal (∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1) :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm
  refine ⟨by rw [hEntropyEq]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hEntropyEq, ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

/-- When the entropy operator is trace-class, entropy is the embedding of its lossless real trace. -/
theorem vonNeumannEntropy_eq_ofReal_entropyOp_realTrace (ρ : DensityOperator H)
    (htrace : IsTraceClass (entropyOp ρ)) :
    vonNeumannEntropy ρ =
      ENNReal.ofReal (htrace.realTrace (entropyOp_isSelfAdjoint ρ)) := by
  rw [vonNeumannEntropy]
  symm
  rw [(hasSum_negMulLog_eigenvalues ρ htrace).tsum_eq.symm]
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun a => Real.negMulLog_nonneg (ρ.eigenvalue_nonneg a) (ρ.eigenvalue_le_one a))
    (hasSum_negMulLog_eigenvalues ρ htrace).summable

end QuantumTheory
