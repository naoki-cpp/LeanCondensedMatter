import LeanCondensedMatter.QuantumTheory.Gibbs.Boltzmann
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula

/-!
# Gibbs states in an energy eigenbasis

Construct the Gibbs density operator on a Hilbert space from an energy eigenbasis and the
scalar Gibbs–Boltzmann data in `Gibbs.Boltzmann`. This also covers summable weights on
infinite-dimensional spaces without requiring a bounded Hamiltonian.
-/

noncomputable section

namespace QuantumTheory

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical pure-point Gibbs density operator.  No bounded Hamiltonian is introduced: the
state is built directly from the spectral Boltzmann weights. -/
noncomputable def eigenbasisGibbsDensityOperator [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) : DensityOperator H :=
  diagonalDensityOperator b (eigenbasisBoltzmannWeight E β) hsum
    (eigenbasisBoltzmannWeight_nonneg E β)
    (by simpa [eigenbasisPartitionFunction] using eigenbasisPartitionFunction_pos E β hsum)

/-- The pure-point Gibbs density operator acts diagonally with the normalized Boltzmann
probabilities. -/
@[simp]
theorem eigenbasisGibbsDensityOperator_apply_basis [Nonempty ι]
    (b : HilbertBasis ι ℂ H) (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) (i : ι) :
    (eigenbasisGibbsDensityOperator b E β hsum).op (b i) =
      (eigenbasisGibbsProbability E β i : ℂ) • b i := by
  have hZ : 0 < ∑' j, eigenbasisBoltzmannWeight E β j := by
    simpa [eigenbasisPartitionFunction] using eigenbasisPartitionFunction_pos E β hsum
  simpa [eigenbasisGibbsDensityOperator, eigenbasisGibbsProbability,
    eigenbasisPartitionFunction, Real.normalizedWeight] using
    diagonalDensityOperator_apply_basis b (eigenbasisBoltzmannWeight E β) hsum
      (eigenbasisBoltzmannWeight_nonneg E β) hZ i

end QuantumTheory
