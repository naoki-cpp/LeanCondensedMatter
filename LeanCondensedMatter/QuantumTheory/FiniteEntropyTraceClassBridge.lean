import LeanCondensedMatter.QuantumTheory.Entropy
import LeanCondensedMatter.QuantumTheory.DiagonalDensityLemmasTraceClass
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-!
# Finite-dimensional entropy bridge to the trace-class API

This module identifies the finite-dimensional density-operator and von Neumann entropy APIs with
the spectral-trace-class versions. The bridge lets finite-dimensional diagonal entropy arguments
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
  have hpos : (ρ.1 : H →L[ℂ] H).IsPositive := ρ.2.1
  have hsymm : (ρ.1 : H →L[ℂ] H).IsSymmetric := hpos.isSelfAdjoint.isSymmetric
  have htrace : LinearMap.trace ℂ H (ρ.1 : H →ₗ[ℂ] H) = 1 := ρ.2.2
  have hcompact : IsCompactOperator (ρ.1 : H →L[ℂ] H) :=
    isCompactOperator_of_locallyCompactSpace_dom (ρ.1 : H →L[ℂ] H)
  letI : Finite (EigenvectorIndex (ρ.1 : H →L[ℂ] H)) :=
    (orthonormal_eigenvectorFamily hcompact hsymm).linearIndependent.finite
  have hsummable : HasSummableRealEigenvalues (ρ.1 : H →L[ℂ] H) := Summable.of_finite
  let hstc : SpectralTraceClass (ρ.1 : H →L[ℂ] H) :=
    SpectralTraceClass.ofPositive hcompact hpos hsummable
  refine
    { op := ρ.1
      pos := hpos
      spectralTraceClass := hstc
      spectralTrace_eq_one := ?_ }
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    hsymm.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ H)) :
      ρ.1 (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i := by
    change (ρ.1 : H →ₗ[ℂ] H) (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i
    simpa [b] using hsymm.apply_eigenvectorBasis rfl i
  have hsum := (hstc.hasSum_inner_apply b.toHilbertBasis).tsum_eq
  rw [tsum_fintype] at hsum
  calc
    hstc.trace = ∑ i, (inner ℂ (b i) (ρ.1 (b i)) : ℂ).re := by
      simpa using hsum.symm
    _ = ∑ i, hsymm.eigenvalues rfl i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      simp
    _ = (LinearMap.trace ℂ H (ρ.1 : H →ₗ[ℂ] H)).re :=
      (hsymm.re_trace_eq_sum_eigenvalues (hn := rfl)).symm
    _ = 1 := by rw [htrace]; norm_num

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
  have heig (i : Fin n) : ρ.1 (b i) = (w i : ℂ) • b i := by
    change (ρ.1 : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i
    simpa [b, w] using ρ.2.1.isSymmetric.apply_eigenvectorBasis hn i
  have happly (i : Fin n) :
      ρ.toTraceClass.op (b.toHilbertBasis i) = (w i : ℂ) • b.toHilbertBasis i := by
    simpa using heig i
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

/-- The finite-dimensional Gibbs entropy equality proved through the trace-class diagonal bridge. -/
theorem vonNeumannEntropy_gibbsState_viaTraceClass [NeZero n]
    (Hop : Observable H) (β : ℝ) :
    vonNeumannEntropy hn (gibbsState hn Hop β) =
      β * energyExpValue (gibbsState hn Hop β) Hop +
        Real.log (partitionFunction hn Hop β) := by
  set Z := partitionFunction hn Hop β with hZ_def
  set E := Hop.2.isSymmetric.eigenvalues hn with hE_def
  set bE := Hop.2.isSymmetric.eigenvectorBasis hn with hbE_def
  set w : Fin n → ℝ := fun i => Real.exp (-β * E i) / Z with hw_def
  have hgibbs_eq : (gibbsState hn Hop β).1 =
      ∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (bE i) (bE i) := rfl
  have hgibbs_apply (j : Fin n) :
      (gibbsState hn Hop β).1 (bE j) = (w j : ℂ) • bE j := by
    rw [hgibbs_eq]
    have happly :
        ((∑ i : Fin n, (w i : ℂ) • InnerProductSpace.rankOne ℂ (bE i) (bE i) :
          H →L[ℂ] H) : H →ₗ[ℂ] H) (bE j) =
          ∑ i : Fin n,
            (w i : ℂ) • InnerProductSpace.rankOne ℂ (bE i) (bE i) (bE j) := by
      simp
    rw [happly, Finset.sum_eq_single j]
    · simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K,
        bE.orthonormal.1 j]
    · intro i _ hij
      simp [InnerProductSpace.rankOne_apply, bE.orthonormal.2 hij]
    · simp
  have hvN : vonNeumannEntropy hn (gibbsState hn Hop β) =
      ∑ i, Real.negMulLog (w i) :=
    vonNeumannEntropy_eq_sum_of_diagonal hn (gibbsState hn Hop β) bE w hgibbs_apply
  have hEbE : ∀ j, (Hop.1 : H →ₗ[ℂ] H) (bE j) = (E j : ℂ) • bE j :=
    fun j => Hop.2.isSymmetric.apply_eigenvectorBasis hn j
  have henergy : energyExpValue (gibbsState hn Hop β) Hop = ∑ i, w i * E i := by
    rw [energyExpValue, hgibbs_eq]
    exact trace_diag_mul_apply_eq_sum bE w E hEbE
  rw [hvN, henergy]
  have hZpos : 0 < Z := partitionFunction_pos hn Hop β
  have hlogw : ∀ i, Real.log (w i) = -β * E i - Real.log Z := by
    intro i
    change Real.log (Real.exp (-β * E i) / Z) = -β * E i - Real.log Z
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hw_sum : ∑ i, w i = 1 := by
    change (∑ i : Fin n, Real.exp (-β * E i) / Z) = 1
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have hexpand : ∑ i, Real.negMulLog (w i) =
      β * ∑ i, w i * E i + Real.log Z * ∑ i, w i := by
    have hterm : ∀ i, Real.negMulLog (w i) =
        β * (w i * E i) + Real.log Z * w i := by
      intro i
      rw [Real.negMulLog, hlogw i]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand, hw_sum, mul_one]

end QuantumTheory
