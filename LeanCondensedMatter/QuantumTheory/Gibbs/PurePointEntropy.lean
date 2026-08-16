import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

/-!
# Entropy identities for pure-point Gibbs data

This module packages the entropy algebra shared by finite-dimensional Gibbs states and countable
pure-point spectral presentations.  The normalized Gibbs weights remain dimension-independent;
finite dimensionality is only one way to discharge their summability and entropy-finiteness
hypotheses.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Hilbert-basis spectral presentation of a bounded Hamiltonian computes the spectral trace of
its Gibbs operator by the corresponding pure-point partition function. -/
theorem purePointPartitionFunction_eq_spectralTrace_gibbsOp
    (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    purePointPartitionFunction E β = spectralTrace (gibbsOp Hop β) := by
  let hGibbs : SpectralTraceClass (gibbsOp Hop β) :=
    SpectralTraceClass.ofPositive hcompact (gibbsOp_isPositive Hop β) hsummable
  have hsum := hGibbs.hasSum_diagonalExpectationValue b
  rw [hGibbs.trace_eq_spectralTrace] at hsum
  have hpoint :
      (fun i => diagonalExpectationValue (gibbsOp Hop β)
        (gibbsOp_isPositive Hop β).isSelfAdjoint (b i)) =
        purePointBoltzmannWeight E β := by
    funext i
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right,
      gibbsOp_apply_eigenvector Hop β (by simpa using hE i),
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp [purePointBoltzmannWeight]
  rw [hpoint] at hsum
  simpa [purePointPartitionFunction] using hsum.tsum_eq

private theorem hasSum_purePointGibbsProbability_of_pos
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β)
    (hZpos : 0 < purePointPartitionFunction E β) :
    HasSum (purePointGibbsProbability E β) 1 := by
  change HasSum
    (fun i => (purePointPartitionFunction E β)⁻¹ * purePointBoltzmannWeight E β i) 1
  have hscaled :=
    (purePointBoltzmannWeight_summable E β hsum).hasSum.mul_left
      (purePointPartitionFunction E β)⁻¹
  change HasSum
    (fun i => (purePointPartitionFunction E β)⁻¹ * purePointBoltzmannWeight E β i)
      ((purePointPartitionFunction E β)⁻¹ * purePointPartitionFunction E β) at hscaled
  rw [inv_mul_cancel₀ hZpos.ne'] at hscaled
  exact hscaled

/-- Any density operator diagonal with normalized pure-point Gibbs weights in a common energy basis
satisfies `S = β E + log Z` once the entropy operator is spectrally summable.  This is the generic
identity specialized by the bounded finite-dimensional Gibbs variational theorem. -/
theorem vonNeumannEntropy_gibbs_diagonal
    (ρ : DensityOperator H) (Hop : Observable H)
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β)
    (hZpos : 0 < purePointPartitionFunction E β)
    (hρ : ∀ i, ρ.op (b i) = (purePointGibbsProbability E β i : ℂ) • b i)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i)
    (hentropy : HasSummableRealEigenvalues (entropyOp ρ)) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      (vonNeumannEntropy ρ).toReal =
        β * energyExpValue ρ Hop + Real.log (purePointPartitionFunction E β) := by
  let p : ι → ℝ := purePointGibbsProbability E β
  let Z : ℝ := purePointPartitionFunction E β
  have hρp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i := by
    intro i
    simpa [p] using hρ i
  have hp_nonneg : ∀ i, 0 ≤ p i := by
    intro i
    exact mul_nonneg (inv_nonneg.mpr hZpos.le) (purePointBoltzmannWeight_nonneg E β i)
  have hp_le_one : ∀ i, p i ≤ 1 :=
    ρ.diagonal_weight_le_one b p hρp hp_nonneg
  have hpSum : HasSum p 1 := by
    simpa [p] using hasSum_purePointGibbsProbability_of_pos E β hsum hZpos
  have hEnergySum := ρ.hasSum_observableExpectation_diagonal Hop b p hρp
  have henergyTerm :
      (fun i => p i * diagonalExpectationValue Hop.1 Hop.2 (b i)) =
        fun i => p i * E i := by
    funext i
    congr 1
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hE i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [henergyTerm, ← energyExpValue_eq_observableExpectation] at hEnergySum
  have hEntropyTraceSum :=
    entropyOpSpectralTraceClass_hasSum_diagonal ρ b p hρp hentropy
  have hlogp (i : ι) : Real.log (p i) = -β * E i - Real.log Z := by
    change Real.log (Z⁻¹ * Real.exp (-β * E i)) = -β * E i - Real.log Z
    rw [show Z⁻¹ * Real.exp (-β * E i) = Real.exp (-β * E i) / Z by
      rw [div_eq_mul_inv, mul_comm]]
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hterm (i : ι) :
      Real.negMulLog (p i) = β * (p i * E i) + Real.log Z * p i := by
    rw [Real.negMulLog, hlogp i]
    ring
  have hEntropyFormula :
      HasSum (fun i => Real.negMulLog (p i))
        (β * energyExpValue ρ Hop + Real.log Z) := by
    have hrhs := (hEnergySum.mul_left β).add (hpSum.mul_left (Real.log Z))
    have hfun :
        (fun i => Real.negMulLog (p i)) =
          fun i => β * (p i * E i) + Real.log Z * p i := by
      funext i
      exact hterm i
    rw [hfun]
    simpa using hrhs
  have htrace :
      (entropyOpSpectralTraceClass ρ hentropy).trace =
        β * energyExpValue ρ Hop + Real.log Z :=
    hEntropyTraceSum.unique hEntropyFormula
  have htrace_nonneg : 0 ≤ (entropyOpSpectralTraceClass ρ hentropy).trace := by
    rw [← hEntropyTraceSum.tsum_eq]
    exact tsum_nonneg fun i => Real.negMulLog_nonneg (hp_nonneg i) (hp_le_one i)
  have hEntropyBridge := vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ hentropy
  constructor
  · rw [hEntropyBridge]
    exact ENNReal.ofReal_ne_top
  · rw [hEntropyBridge, ENNReal.toReal_ofReal htrace_nonneg, htrace]
    rfl

end QuantumTheory
