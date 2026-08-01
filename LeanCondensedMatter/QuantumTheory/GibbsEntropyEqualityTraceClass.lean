import LeanCondensedMatter.QuantumTheory.GibbsEntropyTraceClass

/-!
# Gibbs-state entropy equality via trace-class operators

The normalized Gibbs state attains the trace-class Helmholtz lower bound. Under the current
bounded-Hamiltonian API the compactness assumption on `exp (-βH)` forces finite dimensionality;
the proof evaluates normalization, energy, and entropy against one common energy eigenbasis.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace-class Gibbs state has finite von Neumann entropy and satisfies
`S(ρβ) = β E(ρβ) + log Z`. -/
theorem vonNeumannEntropy_gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace hsummable ≠ 0) :
    vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ) ≠ ⊤ ∧
      (vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ)).toReal =
        β * energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop +
          Real.log (spectralTrace hsummable) := by
  classical
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hsummable hZ
  let Z : ℝ := spectralTrace hsummable
  let E : Fin (Module.finrank ℂ H) → ℝ :=
    Hop.2.isSymmetric.eigenvalues rfl
  let bE : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    Hop.2.isSymmetric.eigenvectorBasis rfl
  let w : Fin (Module.finrank ℂ H) → ℝ := fun i => Real.exp (-β * E i) / Z
  have hZpos : 0 < Z := by
    simpa [Z] using spectralTrace_gibbsOp_pos Hop β hsummable hZ
  have hEbE (i : Fin (Module.finrank ℂ H)) :
      (Hop.1 : H →ₗ[ℂ] H) (bE i) = (E i : ℂ) • bE i := by
    simpa [E, bE] using Hop.2.isSymmetric.apply_eigenvectorBasis rfl i
  have hρbE (i : Fin (Module.finrank ℂ H)) :
      (ρ.op : H →ₗ[ℂ] H) (bE i) = (w i : ℂ) • bE i := by
    simpa [ρ, w, Z, div_eq_mul_inv, mul_comm] using
      (gibbsState_apply_eigenvector Hop β hcompact hsummable hZ (hEbE i))
  have hw_pos (i : Fin (Module.finrank ℂ H)) : 0 < w i := by
    exact div_pos (Real.exp_pos _) hZpos
  have hweight_diag (i : Fin (Module.finrank ℂ H)) :
      (inner ℂ (bE i) (ρ.op (bE i)) : ℂ).re = w i := by
    rw [hρbE i, inner_smul_right, inner_self_eq_norm_sq_to_K, bE.norm_eq_one]
    simp
  have hw_sum : ∑ i, w i = 1 := by
    have hsum := (ρ.hasSum_inner_apply_eq_one bE.toHilbertBasis).tsum_eq
    rw [tsum_fintype] at hsum
    calc
      ∑ i, w i = ∑ i, (inner ℂ (bE i) (ρ.op (bE i)) : ℂ).re := by
        exact Finset.sum_congr rfl fun i _ => (hweight_diag i).symm
      _ = 1 := hsum
  have hw_nonneg (i : Fin (Module.finrank ℂ H)) : 0 ≤ w i := (hw_pos i).le
  have hw_le_one (i : Fin (Module.finrank ℂ H)) : w i ≤ 1 := by
    have hle := (Summable.of_finite : Summable w).le_tsum i
      (fun j _ => hw_nonneg j)
    rw [tsum_fintype, hw_sum] at hle
    exact hle
  let hsEntropy := gibbsState_entropyOp_hasSummableRealEigenvalues
    Hop β hcompact hsummable hZ
  have hEntropyEigen (i : Fin (Module.finrank ℂ H)) :
      entropyOp ρ (bE i) = (Real.negMulLog (w i) : ℂ) • bE i :=
    entropyOp_apply_eigenvector ρ (hρbE i)
  have hEntropyDiag (i : Fin (Module.finrank ℂ H)) :
      (inner ℂ (bE i) (entropyOp ρ (bE i)) : ℂ).re = Real.negMulLog (w i) := by
    rw [hEntropyEigen i, inner_smul_right, inner_self_eq_norm_sq_to_K, bE.norm_eq_one]
    simp
  have hEntropyTrace :
      (entropyOpSpectralTraceClass ρ hsEntropy).trace =
        ∑ i, Real.negMulLog (w i) := by
    have hsum :=
      ((entropyOpSpectralTraceClass ρ hsEntropy).hasSum_inner_apply bE.toHilbertBasis).tsum_eq
    rw [tsum_fintype] at hsum
    calc
      (entropyOpSpectralTraceClass ρ hsEntropy).trace =
          ∑ i, (inner ℂ (bE i) (entropyOp ρ (bE i)) : ℂ).re := hsum.symm
      _ = ∑ i, Real.negMulLog (w i) := by
        exact Finset.sum_congr rfl fun i _ => hEntropyDiag i
  have hEnergyDiag (i : Fin (Module.finrank ℂ H)) :
      (inner ℂ (bE i) ((ρ.op ∘L Hop.1) (bE i)) : ℂ).re = w i * E i := by
    change (inner ℂ (bE i) (ρ.op (Hop.1 (bE i))) : ℂ).re = w i * E i
    rw [hEbE i, map_smul, hρbE i, smul_smul, inner_smul_right,
      inner_self_eq_norm_sq_to_K, bE.norm_eq_one]
    simp
    ring
  have hEnergy : energyExpValue ρ Hop = ∑ i, w i * E i := by
    rw [energyExpValue_eq_re_linearMap_trace]
    rw [LinearMap.trace_eq_sum_inner
      ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) bE]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hEnergyDiag i
  have hEntropyTraceNonneg :
      0 ≤ (entropyOpSpectralTraceClass ρ hsEntropy).trace := by
    rw [hEntropyTrace]
    exact Finset.sum_nonneg fun i _ =>
      Real.negMulLog_nonneg (hw_nonneg i) (hw_le_one i)
  have hlogw (i : Fin (Module.finrank ℂ H)) :
      Real.log (w i) = -β * E i - Real.log Z := by
    change Real.log (Real.exp (-β * E i) / Z) = -β * E i - Real.log Z
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hEntropyExpand :
      ∑ i, Real.negMulLog (w i) =
        β * ∑ i, w i * E i + Real.log Z * ∑ i, w i := by
    have hterm : ∀ i, Real.negMulLog (w i) =
        β * (w i * E i) + Real.log Z * w i := by
      intro i
      rw [Real.negMulLog, hlogw i]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hEntropyBridge := vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ hsEntropy
  change vonNeumannEntropy ρ ≠ ⊤ ∧
    (vonNeumannEntropy ρ).toReal = β * energyExpValue ρ Hop + Real.log Z
  constructor
  · rw [hEntropyBridge]
    exact ENNReal.ofReal_ne_top
  · rw [hEntropyBridge, ENNReal.toReal_ofReal hEntropyTraceNonneg,
      hEntropyTrace, hEnergy, hEntropyExpand, hw_sum, mul_one]

end QuantumTheory.TraceClass
