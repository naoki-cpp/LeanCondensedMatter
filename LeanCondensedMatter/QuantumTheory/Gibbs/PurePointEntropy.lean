import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePointExpectation

/-!
# Entropy and free energy of countable pure-point Gibbs states

For a countable pure-point Gibbs state, absolute integrability of the energy series is enough to
make the entropy series absolutely summable. The resulting von Neumann entropy therefore satisfies
the canonical Gibbs identity without representing the potentially unbounded energy data by a
bounded observable.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem purePointGibbsProbability_le_one [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β) (i : ι) :
    purePointGibbsProbability E β i ≤ 1 := by
  have hprob := hasSum_purePointGibbsProbability E β hsum
  have hle := hprob.summable.le_tsum i
    (fun j _ => purePointGibbsProbability_nonneg E β hsum j)
  rw [hprob.tsum_eq] at hle
  exact hle

/-- Absolute energy integrability implies absolute summability of the Shannon entropy terms of the
pure-point Gibbs probabilities. -/
theorem summable_norm_negMulLog_purePointGibbsProbability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    Summable fun i => ‖Real.negMulLog (purePointGibbsProbability E β i)‖ := by
  let Z := purePointPartitionFunction E β
  have hZpos : 0 < Z := by
    simpa [Z] using purePointPartitionFunction_pos E β hsum
  have hEnergy : Summable fun i => purePointGibbsProbability E β i * E i :=
    Summable.of_norm hint
  have hProb := (hasSum_purePointGibbsProbability E β hsum).summable
  have hlog (i : ι) :
      Real.log (purePointGibbsProbability E β i) =
        -β * E i - Real.log Z := by
    rw [purePointGibbsProbability, purePointBoltzmannWeight,
      Real.log_mul (inv_ne_zero hZpos.ne') (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp]
    rfl
  have hterm (i : ι) :
      Real.negMulLog (purePointGibbsProbability E β i) =
        β * (purePointGibbsProbability E β i * E i) +
          Real.log Z * purePointGibbsProbability E β i := by
    rw [Real.negMulLog, hlog i]
    ring
  have hEntropy : Summable fun i =>
      Real.negMulLog (purePointGibbsProbability E β i) := by
    exact ((hEnergy.mul_left β).add (hProb.mul_left (Real.log Z))).congr
      (fun i => (hterm i).symm)
  exact hEntropy.congr fun i => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.negMulLog_nonneg
        (purePointGibbsProbability_nonneg E β hsum i)
        (purePointGibbsProbability_le_one E β hsum i))]

/-- A countable pure-point Gibbs state with absolutely integrable energy has finite von Neumann
entropy and satisfies `S = β ⟨E⟩ + log Z`. -/
theorem vonNeumannEntropy_purePointGibbsDensityOperator [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    vonNeumannEntropy (purePointGibbsDensityOperator b E β hsum) ≠ ⊤ ∧
      (vonNeumannEntropy (purePointGibbsDensityOperator b E β hsum)).toReal =
        β * purePointGibbsEnergyExpectation E β +
          Real.log (purePointPartitionFunction E β) := by
  let ρ := purePointGibbsDensityOperator b E β hsum
  let p := purePointGibbsProbability E β
  let Z := purePointPartitionFunction E β
  have hρ : ∀ i, ρ.op (b i) = (p i : ℂ) • b i := by
    intro i
    simpa [ρ, p] using purePointGibbsDensityOperator_apply_basis b E β hsum i
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => by
    simpa [p] using purePointGibbsProbability_nonneg E β hsum i
  have hp_le_one : ∀ i, p i ≤ 1 :=
    ρ.diagonal_weight_le_one b p hρ hp_nonneg
  have hentropy : HasSummableRealEigenvalues (entropyOp ρ) :=
    ρ.entropyOp_hasSummableRealEigenvalues_of_diagonal b p hρ (by
      simpa [p] using summable_norm_negMulLog_purePointGibbsProbability E β hsum hint)
  have hEntropySum :=
    entropyOpSpectralTraceClass_hasSum_diagonal ρ b p hρ hentropy
  have hEnergySum :=
    hasSum_purePointGibbsEnergyExpectation E β hint
  have hProbSum := hasSum_purePointGibbsProbability E β hsum
  have hZpos : 0 < Z := by
    simpa [Z] using purePointPartitionFunction_pos E β hsum
  have hlog (i : ι) :
      Real.log (p i) = -β * E i - Real.log Z := by
    simp only [p]
    rw [purePointGibbsProbability, purePointBoltzmannWeight,
      Real.log_mul (inv_ne_zero hZpos.ne') (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp]
    rfl
  have hterm (i : ι) :
      Real.negMulLog (p i) =
        β * (p i * E i) + Real.log Z * p i := by
    rw [Real.negMulLog, hlog i]
    ring
  have hEntropyFormula :
      HasSum (fun i => Real.negMulLog (p i))
        (β * purePointGibbsEnergyExpectation E β + Real.log Z) := by
    simpa [p] using HasSum.congr_fun
      ((hEnergySum.mul_left β).add (hProbSum.mul_left (Real.log Z))) hterm
  have htrace :
      (entropyOpSpectralTraceClass ρ hentropy).trace =
        β * purePointGibbsEnergyExpectation E β + Real.log Z :=
    hEntropySum.unique hEntropyFormula
  have htrace_nonneg : 0 ≤ (entropyOpSpectralTraceClass ρ hentropy).trace := by
    rw [← hEntropySum.tsum_eq]
    exact tsum_nonneg fun i => Real.negMulLog_nonneg (hp_nonneg i) (hp_le_one i)
  have hEntropyBridge := vonNeumannEntropy_eq_ofReal_entropyOp_trace ρ hentropy
  change vonNeumannEntropy ρ ≠ ⊤ ∧
    (vonNeumannEntropy ρ).toReal =
      β * purePointGibbsEnergyExpectation E β + Real.log Z
  constructor
  · rw [hEntropyBridge]
    exact ENNReal.ofReal_ne_top
  · rw [hEntropyBridge, ENNReal.toReal_ofReal htrace_nonneg, htrace]

/-- For nonzero inverse temperature, the countable pure-point Gibbs state satisfies the exact
Helmholtz free-energy identity. -/
theorem purePointGibbs_helmholtzFreeEnergy_eq [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hsum : PurePointGibbsSummable E β)
    (hint : PurePointGibbsEnergyIntegrable E β) :
    purePointGibbsEnergyExpectation E β -
        (1 / β) * (vonNeumannEntropy
          (purePointGibbsDensityOperator b E β hsum)).toReal =
      -(1 / β) * Real.log (purePointPartitionFunction E β) := by
  have hEntropy :=
    (vonNeumannEntropy_purePointGibbsDensityOperator b E β hsum hint).2
  rw [hEntropy, mul_add]
  have hscale :
      (1 / β) * (β * purePointGibbsEnergyExpectation E β) =
        purePointGibbsEnergyExpectation E β := by
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hβ, one_mul]
  rw [hscale]
  ring

end QuantumTheory
