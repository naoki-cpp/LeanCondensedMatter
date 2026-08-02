import LeanCondensedMatter.QuantumTheory.Entropy
import LeanCondensedMatter.QuantumTheory.DiagonalDensityLemmasTraceClass
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Finite-dimensional entropy bridge to the trace-class API

This module identifies the finite-dimensional density-operator and von Neumann entropy APIs with
the spectral-trace-class versions.  The bridge lets finite-dimensional diagonal entropy arguments
reuse the same Hilbert-basis formulas as the infinite-dimensional theory, without matching a
hand-built diagonal presentation to Mathlib's sorted eigenvalue list through characteristic
polynomials.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]
variable {n : ℕ} (hn : Module.finrank ℂ H = n)

/-- Regard a finite-dimensional density operator as a spectral-trace-class density operator. -/
def DensityOperator.toTraceClass (ρ : DensityOperator H) : TraceClass.DensityOperator H := by
  have hcompact : IsCompactOperator (ρ.1 : H →L[ℂ] H) :=
    isCompactOperator_of_finiteDimensional
  have hsymm : (ρ.1 : H →L[ℂ] H).IsSymmetric := ρ.2.1.isSelfAdjoint.isSymmetric
  letI : Finite (EigenvectorIndex (ρ.1 : H →L[ℂ] H)) :=
    (orthonormal_eigenvectorFamily hcompact hsymm).linearIndependent.finite
  have hsummable : HasSummableRealEigenvalues (ρ.1 : H →L[ℂ] H) := Summable.of_finite
  let hstc : SpectralTraceClass (ρ.1 : H →L[ℂ] H) :=
    SpectralTraceClass.ofPositive hcompact ρ.2.1 hsummable
  refine
    { op := ρ.1
      pos := ρ.2.1
      spectralTraceClass := hstc
      spectralTrace_eq_one := ?_ }
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    ρ.2.1.isSymmetric.eigenvectorBasis rfl
  have hsum := (hstc.hasSum_inner_apply b.toHilbertBasis).tsum_eq
  rw [tsum_fintype] at hsum
  calc
    hstc.trace = ∑ i, (inner ℂ (b i) (ρ.1 (b i)) : ℂ).re := hsum.symm
    _ = (LinearMap.trace ℂ H (ρ.1 : H →ₗ[ℂ] H)).re := by
      rw [LinearMap.trace_eq_sum_inner (ρ.1 : H →ₗ[ℂ] H) b]
      simpa only [Complex.reCLM_apply] using
        (map_sum Complex.reCLM (fun i => inner ℂ (b i) (ρ.1 (b i))) Finset.univ).symm
    _ = 1 := by rw [ρ.2.2]; norm_num

@[simp] theorem DensityOperator.toTraceClass_op (ρ : DensityOperator H) :
    ρ.toTraceClass.op = ρ.1 := rfl

/-- In finite dimensions the entropy operator automatically has summable nonzero eigenvalues. -/
theorem DensityOperator.toTraceClass_entropyOp_hasSummableRealEigenvalues
    (ρ : DensityOperator H) :
    HasSummableRealEigenvalues (TraceClass.entropyOp ρ.toTraceClass) := by
  have hcompact : IsCompactOperator (TraceClass.entropyOp ρ.toTraceClass) :=
    TraceClass.entropyOp_isCompact ρ.toTraceClass
  have hself : IsSelfAdjoint (TraceClass.entropyOp ρ.toTraceClass) := by
    rw [TraceClass.entropyOp]
    exact cfc_predicate _ _
  letI : Finite (EigenvectorIndex (TraceClass.entropyOp ρ.toTraceClass)) :=
    (orthonormal_eigenvectorFamily hcompact hself.isSymmetric).linearIndependent.finite
  exact Summable.of_finite

/-- The finite-dimensional entropy equals the spectral trace of the trace-class entropy operator. -/
theorem vonNeumannEntropy_eq_entropyOp_spectralTrace (ρ : DensityOperator H) :
    vonNeumannEntropy hn ρ =
      (TraceClass.entropyOpSpectralTraceClass ρ.toTraceClass
        ρ.toTraceClass_entropyOp_hasSummableRealEigenvalues).trace := by
  let b : OrthonormalBasis (Fin n) ℂ H := ρ.2.1.isSymmetric.eigenvectorBasis hn
  let w : Fin n → ℝ := ρ.2.1.isSymmetric.eigenvalues hn
  have happly (i : Fin n) :
      ρ.toTraceClass.op (b i) = (w i : ℂ) • b i := by
    simpa [b, w] using ρ.2.1.isSymmetric.apply_eigenvectorBasis hn i
  have htrace := TraceClass.entropyOpSpectralTraceClass_trace_eq_tsum_diagonal
    ρ.toTraceClass b.toHilbertBasis w happly
    ρ.toTraceClass_entropyOp_hasSummableRealEigenvalues
  rw [tsum_fintype] at htrace
  simpa [vonNeumannEntropy, w] using htrace.symm

/-- A diagonal presentation computes finite-dimensional von Neumann entropy directly. -/
theorem vonNeumannEntropy_eq_sum_of_diagonal (ρ : DensityOperator H)
    (b : OrthonormalBasis (Fin n) ℂ H) (w : Fin n → ℝ)
    (happly : ∀ i, ρ.1 (b i) = (w i : ℂ) • b i) :
    vonNeumannEntropy hn ρ = ∑ i, Real.negMulLog (w i) := by
  rw [vonNeumannEntropy_eq_entropyOp_spectralTrace hn ρ]
  have htrace := TraceClass.entropyOpSpectralTraceClass_trace_eq_tsum_diagonal
    ρ.toTraceClass b.toHilbertBasis w (fun i => by simpa using happly i)
    ρ.toTraceClass_entropyOp_hasSummableRealEigenvalues
  simpa only [tsum_fintype] using htrace

end QuantumTheory
