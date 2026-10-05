import LeanCondensedMatter.QuantumTheory.Gibbs.FreeEnergy
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal

/-!
# Gibbs-state entropy

Dimension-independent entropy algebra for Gibbs-diagonal density states, together with the bounded
Gibbs-state eigenvector formula. For a bounded energy observable, normalization and the energy
expectation make entropy summability a derived property rather than a separate hypothesis.
-/

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A density state with Gibbs weights `exp (-β Eᵢ) / Z` in a common energy basis satisfies
`S = β E + log Z`. For a bounded energy observable, the Gibbs identity itself gives the
summability needed to make the entropy operator trace-class. -/
theorem vonNeumannEntropy_gibbs_diagonal
    (ρ : DensityOperator H) (Hop : Observable H) (b : HilbertBasis ι ℂ H)
    (E : ι → ℝ) (β Z : ℝ) (hZ : 0 < Z)
    (hρ : ∀ i, ρ.op (b i) = ((Real.exp (-β * E i) / Z : ℝ) : ℂ) • b i)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    vonNeumannEntropy ρ ≠ ⊤ ∧
      (vonNeumannEntropy ρ).toReal = β * energyExpValue ρ Hop + Real.log Z := by
  let w : ι → ℝ := fun i => Real.exp (-β * E i) / Z
  have hρw : ∀ i, ρ.op (b i) = (w i : ℂ) • b i := by
    intro i
    simpa [w] using hρ i
  have hwSum := ρ.hasSum_diagonal_weights b w hρw
  have hEnergySum : HasSum (fun i => w i * E i) (energyExpValue ρ Hop) := by
    change HasSum (fun i => w i * E i) (ρ.observableExpectation Hop)
    exact HasSum.congr_fun (ρ.hasSum_observableExpectation_diagonal Hop b w hρw) fun i => by
      symm
      congr 1
      apply Complex.ofReal_injective
      rw [coe_diagonalExpectationValue_right, hE i, inner_smul_right,
        inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
  have hlogw (i : ι) : Real.log (w i) = -β * E i - Real.log Z := by
    change Real.log (Real.exp (-β * E i) / Z) = -β * E i - Real.log Z
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  have hterm (i : ι) :
      Real.negMulLog (w i) = β * (w i * E i) + Real.log Z * w i := by
    rw [Real.negMulLog, hlogw i]
    ring
  have hEntropyFormula :
      HasSum (fun i => Real.negMulLog (w i))
        (β * energyExpValue ρ Hop + Real.log Z) := by
    simpa using HasSum.congr_fun
      ((hEnergySum.mul_left β).add (hwSum.mul_left (Real.log Z))) hterm
  exact ρ.vonNeumannEntropy_ne_top_and_toReal_eq_of_hasSum_diagonal
    b w hρw hEntropyFormula

/-- The normalized Gibbs state acts diagonally on every energy eigenvector. -/
theorem gibbsState_apply_eigenvector [Nontrivial H] [FiniteDimensional ℂ H]
    (Hop : Observable H) (β : ℝ) {v : H} {E : ℝ}
    (hv : (Hop.1 : H →ₗ[ℂ] H) v = (E : ℂ) • v) :
    (gibbsState Hop β).op v =
      (((spectralTrace (gibbsOp Hop β))⁻¹ : ℝ) • (Real.exp (-β * E) : ℂ)) • v := by
  rw [gibbsState_op Hop β, smul_apply, gibbsOp_apply_eigenvector Hop β hv]
  exact (smul_assoc ((spectralTrace (gibbsOp Hop β))⁻¹ : ℝ)
    (Real.exp (-β * E) : ℂ) v).symm

end QuantumTheory
