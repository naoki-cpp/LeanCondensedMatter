import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Gibbs.EigenbasisExpectation

/-!
# Entropy and free energy in an energy eigenbasis

For a countable pure-point Gibbs state, absolute integrability of the energy series is enough to
make the entropy series absolutely summable. The resulting von Neumann entropy therefore satisfies
the Gibbs entropy identity without representing the potentially unbounded energy data by a
bounded observable.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pointwise Shannon-entropy identity for normalized pure-point Gibbs weights. -/
private theorem negMulLog_eigenbasisGibbsProbability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β) (i : ι) :
    Real.negMulLog (eigenbasisGibbsProbability E β i) =
      β * (eigenbasisGibbsProbability E β i * E i) +
        Real.log (eigenbasisPartitionFunction E β) *
          eigenbasisGibbsProbability E β i := by
  have hZpos := eigenbasisPartitionFunction_pos E β hsum
  have hlog :
      Real.log (eigenbasisGibbsProbability E β i) =
        -β * E i - Real.log (eigenbasisPartitionFunction E β) := by
    rw [eigenbasisGibbsProbability, eigenbasisBoltzmannWeight,
      Real.log_mul (inv_ne_zero hZpos.ne') (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp]
    ring
  rw [Real.negMulLog, hlog]
  ring

/-- Absolute energy integrability implies absolute summability of the Shannon entropy terms of the
pure-point Gibbs probabilities. -/
theorem summable_norm_negMulLog_eigenbasisGibbsProbability [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    Summable fun i => ‖Real.negMulLog (eigenbasisGibbsProbability E β i)‖ := by
  let Z := eigenbasisPartitionFunction E β
  have hEnergy : Summable fun i => eigenbasisGibbsProbability E β i * E i :=
    Summable.of_norm hint
  have hProb := (hasSum_eigenbasisGibbsProbability E β hsum).summable
  have hEntropy : Summable fun i =>
      Real.negMulLog (eigenbasisGibbsProbability E β i) := by
    exact ((hEnergy.mul_left β).add (hProb.mul_left (Real.log Z))).congr
      (fun i => by
        simpa [Z] using (negMulLog_eigenbasisGibbsProbability E β hsum i).symm)
  exact hEntropy.norm

/-- A countable pure-point Gibbs state with absolutely integrable energy has finite von Neumann
entropy and satisfies `S = β ⟨E⟩ + log Z`. -/
theorem vonNeumannEntropy_eigenbasisGibbsDensityOperator [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    vonNeumannEntropy (eigenbasisGibbsDensityOperator b E β hsum) ≠ ⊤ ∧
      (vonNeumannEntropy (eigenbasisGibbsDensityOperator b E β hsum)).toReal =
        β * eigenbasisGibbsEnergyExpectation E β +
          Real.log (eigenbasisPartitionFunction E β) := by
  let ρ := eigenbasisGibbsDensityOperator b E β hsum
  let p := eigenbasisGibbsProbability E β
  let Z := eigenbasisPartitionFunction E β
  have hρ : ∀ i, ρ.op (b i) = (p i : ℂ) • b i := by
    intro i
    simpa [ρ, p] using eigenbasisGibbsDensityOperator_apply_basis b E β hsum i
  have hEnergySum :=
    hasSum_eigenbasisGibbsEnergyExpectation E β hint
  have hProbSum := hasSum_eigenbasisGibbsProbability E β hsum
  have hEntropyFormula :
      HasSum (fun i => Real.negMulLog (p i))
        (β * eigenbasisGibbsEnergyExpectation E β + Real.log Z) := by
    simpa [p] using HasSum.congr_fun
      ((hEnergySum.mul_left β).add (hProbSum.mul_left (Real.log Z))) fun i => by
        simpa [p, Z] using negMulLog_eigenbasisGibbsProbability E β hsum i
  change vonNeumannEntropy ρ ≠ ⊤ ∧
    (vonNeumannEntropy ρ).toReal =
      β * eigenbasisGibbsEnergyExpectation E β + Real.log Z
  exact ρ.vonNeumannEntropy_ne_top_and_toReal_eq_of_hasSum_diagonal
    b p hρ hEntropyFormula

/-- For nonzero inverse temperature, the countable pure-point Gibbs state satisfies the exact
Helmholtz free-energy identity. -/
theorem eigenbasisGibbs_helmholtzFreeEnergy_eq [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hsum : EigenbasisGibbsSummable E β)
    (hint : EigenbasisGibbsEnergyIntegrable E β) :
    eigenbasisGibbsEnergyExpectation E β -
        (1 / β) * (vonNeumannEntropy
          (eigenbasisGibbsDensityOperator b E β hsum)).toReal =
      -(1 / β) * Real.log (eigenbasisPartitionFunction E β) := by
  rw [(vonNeumannEntropy_eigenbasisGibbsDensityOperator b E β hsum hint).2]
  field_simp [hβ]
  ring

end QuantumTheory
