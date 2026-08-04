import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Gibbs.DiagonalEnergy

/-!
# Gibbs-state variational equality

The normalized Gibbs state attains the Helmholtz lower bound. Under the bounded-Hamiltonian API,
compactness of `exp (-βH)` forces finite dimensionality, so one common energy eigenbasis can be used.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs state has finite entropy and satisfies `S(ρβ) = β E(ρβ) + log Z`. -/
theorem vonNeumannEntropy_gibbsState (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ) ≠ ⊤ ∧
      (vonNeumannEntropy (gibbsState Hop β hcompact hsummable hZ)).toReal =
        β * energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop +
          Real.log (spectralTrace (gibbsOp Hop β)) := by
  classical
  letI := finiteDimensional_of_gibbsOp_isCompact Hop β hcompact
  let ρ := gibbsState Hop β hcompact hsummable hZ
  let Z : ℝ := spectralTrace (gibbsOp Hop β)
  let E : Fin (Module.finrank ℂ H) → ℝ :=
    Hop.2.isSymmetric.eigenvalues rfl
  let bE : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    Hop.2.isSymmetric.eigenvectorBasis rfl
  let w : Fin (Module.finrank ℂ H) → ℝ := fun i => Real.exp (-β * E i) / Z
  have hZpos : 0 < Z := by
    simpa [Z] using spectralTrace_gibbsOp_pos Hop β hZ
  have hEbE (i : Fin (Module.finrank ℂ H)) :
      (Hop.1 : H →ₗ[ℂ] H) (bE i) = (E i : ℂ) • bE i := by
    simpa [E, bE] using Hop.2.isSymmetric.apply_eigenvectorBasis rfl i
  have hρbE (i : Fin (Module.finrank ℂ H)) :
      (ρ.op : H →ₗ[ℂ] H) (bE i) = (w i : ℂ) • bE i := by
    simpa [ρ, w, Z, div_eq_mul_inv, mul_comm] using
      (gibbsState_apply_eigenvector Hop β hcompact hsummable hZ (hEbE i))
  have hw_pos (i : Fin (Module.finrank ℂ H)) : 0 < w i := by
    exact div_pos (Real.exp_pos _) hZpos
  have hw_sum : ∑ i, w i = 1 := by
    have hsum :=
      (ρ.hasSum_diagonal_weights bE.toHilbertBasis w
        (fun i => by simpa using hρbE i)).tsum_eq
    simpa only [tsum_fintype] using hsum
  have hw_nonneg (i : Fin (Module.finrank ℂ H)) : 0 ≤ w i := (hw_pos i).le
  have hw_le_one (i : Fin (Module.finrank ℂ H)) : w i ≤ 1 :=
    ρ.diagonal_weight_le_one bE.toHilbertBasis w
      (fun j => by simpa using hρbE j) hw_nonneg i
  let hsEntropy := gibbsState_entropyOp_hasSummableRealEigenvalues
    Hop β hcompact hsummable hZ
  have hEntropyTrace :
      (entropyOpSpectralTraceClass ρ hsEntropy).trace =
        ∑ i, Real.negMulLog (w i) := by
    have htrace := entropyOpSpectralTraceClass_trace_eq_tsum_diagonal
      ρ bE.toHilbertBasis w (fun i => by simpa using hρbE i) hsEntropy
    simpa only [tsum_fintype] using htrace
  have hEnergy : energyExpValue ρ Hop = ∑ i, w i * E i :=
    energyExpValue_eq_sum_common_eigenbasis ρ Hop bE w E hρbE hEbE
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

/-- The normalized Gibbs state attains the Helmholtz lower bound exactly. -/
theorem gibbsState_helmholtzFreeEnergy_eq (Hop : Observable H) (β : ℝ) (hβ : 0 < β)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hsummable hZ)).toReal =
      -(1 / β) * Real.log (spectralTrace (gibbsOp Hop β)) := by
  have hEntropy :=
    (vonNeumannEntropy_gibbsState Hop β hcompact hsummable hZ).2
  rw [hEntropy, mul_add]
  have hβne : β ≠ 0 := hβ.ne'
  have hscale :
      (1 / β) *
          (β * energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop) =
        energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hβne, one_mul]
  rw [hscale]
  ring

/-- Every density operator has Helmholtz free energy at least that of the normalized Gibbs state. -/
theorem gibbsState_minimizes_helmholtzFreeEnergy (ρ : DensityOperator H) (Hop : Observable H)
    (β : ℝ) (hβ : 0 < β) (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :
    energyExpValue (gibbsState Hop β hcompact hsummable hZ) Hop -
        (1 / β) * (vonNeumannEntropy
          (gibbsState Hop β hcompact hsummable hZ)).toReal ≤
      energyExpValue ρ Hop - (1 / β) * (vonNeumannEntropy ρ).toReal := by
  rw [gibbsState_helmholtzFreeEnergy_eq Hop β hβ hcompact hsummable hZ]
  exact (helmholtzFreeEnergy_ge_and_entropy_ne_top
    ρ Hop β hβ hcompact hsummable hZ).2

end QuantumTheory
