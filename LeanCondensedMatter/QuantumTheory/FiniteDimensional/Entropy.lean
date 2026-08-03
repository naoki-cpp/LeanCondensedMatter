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

/-- In finite dimensions, the entropy operator has summable nonzero real eigenvalues. -/
theorem DensityOperator.entropyOp_hasSummableRealEigenvalues (ρ : DensityOperator H) :
    HasSummableRealEigenvalues (entropyOp ρ) := by
  have hcompact : IsCompactOperator (entropyOp ρ) := entropyOp_isCompact ρ
  have hselfAdjoint : IsSelfAdjoint (entropyOp ρ) := by
    rw [entropyOp]
    exact cfc_predicate _ _
  letI : Finite (EigenvectorIndex (entropyOp ρ)) :=
    (orthonormal_eigenvectorFamily hcompact hselfAdjoint.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

/-- The canonical von Neumann entropy is finite in finite dimensions. -/
theorem DensityOperator.vonNeumannEntropy_ne_top (ρ : DensityOperator H) :
    vonNeumannEntropy ρ ≠ ⊤ := by
  rw [vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ ρ.entropyOp_hasSummableRealEigenvalues]
  exact ENNReal.ofReal_ne_top

/-- In finite dimensions, the real value of the canonical entropy is the eigenvalue sum. -/
theorem DensityOperator.vonNeumannEntropy_toReal_eq_tsum (ρ : DensityOperator H) :
    (vonNeumannEntropy ρ).toReal =
      ∑' a : EigenvectorIndex ρ.op, Real.negMulLog a.1.1 := by
  let hs := ρ.entropyOp_hasSummableRealEigenvalues
  rw [vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ hs,
    entropyOp_trace_eq_tsum ρ hs]
  exact ENNReal.toReal_ofReal
    (tsum_nonneg fun a =>
      Real.negMulLog_nonneg (eigenvalue_nonneg ρ a) (density_eigenvalue_le_one ρ a))

end QuantumTheory
