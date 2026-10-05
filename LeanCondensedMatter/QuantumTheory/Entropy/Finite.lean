import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Finite-dimensional entropy specialization

Finite dimensionality does not introduce a second density-state or entropy type. It proves that the
canonical `ENNReal`-valued entropy is finite and identifies its real value with the eigenvalue sum.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- In finite dimensions, the entropy operator is trace-class. -/
theorem DensityOperator.entropyOp_isTraceClass (ρ : DensityOperator H) :
    IsTraceClass (entropyOp ρ) := by
  have hcompact : IsCompactOperator (entropyOp ρ) := entropyOp_isCompact ρ
  have hselfAdjoint : IsSelfAdjoint (entropyOp ρ) := entropyOp_isSelfAdjoint ρ
  apply (isTraceClass_iff_hasSummableRealEigenvalues hcompact hselfAdjoint).2
  letI : Finite (EigenvectorIndex (entropyOp ρ)) :=
    (orthonormal_eigenvectorFamily hcompact hselfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

/-- The canonical von Neumann entropy is finite in finite dimensions. -/
theorem DensityOperator.vonNeumannEntropy_ne_top (ρ : DensityOperator H) :
    vonNeumannEntropy ρ ≠ ⊤ := by
  exact (vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ
    (hasSum_negMulLog_eigenvalues ρ ρ.entropyOp_isTraceClass).summable).1

/-- In finite dimensions, the real value of the canonical entropy is the eigenvalue sum. -/
theorem DensityOperator.vonNeumannEntropy_toReal_eq_tsum (ρ : DensityOperator H) :
    (vonNeumannEntropy ρ).toReal =
      ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 := by
  exact (vonNeumannEntropy_ne_top_and_toReal_eq_tsum ρ
    (hasSum_negMulLog_eigenvalues ρ ρ.entropyOp_isTraceClass).summable).2

end QuantumTheory
