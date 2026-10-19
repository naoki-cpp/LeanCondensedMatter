import LeanCondensedMatter.Analysis.InfiniteSum.Normalization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gibbs–Boltzmann weights and partition function

The Boltzmann weight, its partition sum, the normalized Gibbs probabilities, and their
summability requirements depend only on a family of real energies and inverse temperature.
No Hilbert basis, bounded Hamiltonian, or density operator is required.

The explicit summability hypothesis supports countable energy families; integrability of
energy-weighted probabilities is a separate condition for finite mean energy.
-/

noncomputable section

namespace QuantumTheory

variable {ι : Type*}

/-- The positive real Boltzmann weight `exp (-β Eᵢ)` attached to one pure-point energy level. -/
noncomputable def eigenbasisBoltzmannWeight (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i)

theorem eigenbasisBoltzmannWeight_pos (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 < eigenbasisBoltzmannWeight E β i := by
  simpa [eigenbasisBoltzmannWeight] using Real.exp_pos (-β * E i)

theorem eigenbasisBoltzmannWeight_nonneg (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ eigenbasisBoltzmannWeight E β i :=
  (eigenbasisBoltzmannWeight_pos E β i).le

/-- Absolute Boltzmann summability for a pure-point Gibbs state.  This is the explicit trace-class
hypothesis consumed by the generic diagonal density-state constructor. -/
def EigenbasisGibbsSummable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖eigenbasisBoltzmannWeight E β i‖

/-- The pure-point partition function `Z(β) = ∑ᵢ exp (-β Eᵢ)`. -/
noncomputable def eigenbasisPartitionFunction (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑' i, eigenbasisBoltzmannWeight E β i

/-- Absolute Boltzmann summability implies ordinary summability of the positive weights. -/
theorem eigenbasisBoltzmannWeight_summable (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    Summable (eigenbasisBoltzmannWeight E β) :=
  Summable.of_norm hsum

/-- For a nonempty pure-point spectrum, a summable family of strictly positive Boltzmann weights
has a strictly positive partition function. -/
theorem eigenbasisPartitionFunction_pos [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    0 < eigenbasisPartitionFunction E β := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  rw [eigenbasisPartitionFunction]
  exact (eigenbasisBoltzmannWeight_summable E β hsum).tsum_pos
    (fun j => eigenbasisBoltzmannWeight_nonneg E β j) i
    (eigenbasisBoltzmannWeight_pos E β i)

/-- The normalized Gibbs probability of one pure-point energy level. -/
noncomputable def eigenbasisGibbsProbability (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  (eigenbasisPartitionFunction E β)⁻¹ * eigenbasisBoltzmannWeight E β i

theorem eigenbasisGibbsProbability_nonneg (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ eigenbasisGibbsProbability E β i := by
  unfold eigenbasisGibbsProbability
  exact mul_nonneg
    (inv_nonneg.mpr (by
      rw [eigenbasisPartitionFunction]
      exact tsum_nonneg fun j => eigenbasisBoltzmannWeight_nonneg E β j))
    (eigenbasisBoltzmannWeight_nonneg E β i)

/-- The normalized pure-point Gibbs probabilities sum to one. -/
theorem hasSum_eigenbasisGibbsProbability [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    HasSum (eigenbasisGibbsProbability E β) 1 := by
  exact
    Real.hasSum_normalizedWeight (eigenbasisBoltzmannWeight E β)
      (eigenbasisBoltzmannWeight_summable E β hsum)
      (eigenbasisPartitionFunction_pos E β hsum).ne'

/-- Finiteness condition for the mean energy when the pure-point energy data are not represented by
a bounded `Observable`.  State existence alone does not imply this stronger weighted summability. -/
def EigenbasisGibbsEnergyIntegrable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖eigenbasisGibbsProbability E β i * E i‖

/-- On a finite spectral index, the Boltzmann summability hypothesis is automatic. -/
theorem eigenbasisGibbsSummable_of_finite [Finite ι] (E : ι → ℝ) (β : ℝ) :
    EigenbasisGibbsSummable E β := by
  exact Summable.of_finite

end QuantumTheory
