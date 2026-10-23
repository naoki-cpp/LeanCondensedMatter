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

/-- The positive real Boltzmann weight `exp (-β Eᵢ)` of an energy level. -/
noncomputable def eigenbasisBoltzmannWeight (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * E i)

theorem eigenbasisBoltzmannWeight_pos (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 < eigenbasisBoltzmannWeight E β i := by
  simpa [eigenbasisBoltzmannWeight] using Real.exp_pos (-β * E i)

theorem eigenbasisBoltzmannWeight_nonneg (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ eigenbasisBoltzmannWeight E β i :=
  (eigenbasisBoltzmannWeight_pos E β i).le


/-- Adding a common energy offset multiplies each Boltzmann weight by the
same positive factor. -/
theorem eigenbasisBoltzmannWeight_add_const (E : ι → ℝ) (β c : ℝ) (i : ι) :
    eigenbasisBoltzmannWeight (fun j => E j + c) β i =
      Real.exp (-β * c) * eigenbasisBoltzmannWeight E β i := by
  simp only [eigenbasisBoltzmannWeight]
  rw [show -β * (E i + c) = -β * c + -β * E i by ring, Real.exp_add]

/-- Absolute Boltzmann summability. This guarantees a finite partition function and, when
combined with a Hilbert basis, a trace-class Gibbs density operator. -/
def EigenbasisGibbsSummable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖eigenbasisBoltzmannWeight E β i‖


/-- A common energy offset preserves absolute Boltzmann summability. -/
theorem eigenbasisGibbsSummable_add_const (E : ι → ℝ) (β c : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    EigenbasisGibbsSummable (fun i => E i + c) β := by
  change Summable (fun i =>
    ‖eigenbasisBoltzmannWeight (fun j => E j + c) β i‖)
  have h : Summable (fun i =>
      Real.exp (-β * c) * ‖eigenbasisBoltzmannWeight E β i‖) :=
    hsum.mul_left (Real.exp (-β * c))
  apply h.congr
  intro i
  rw [eigenbasisBoltzmannWeight_add_const, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The partition function `Z(β) = ∑ᵢ exp (-β Eᵢ)`. -/
noncomputable def eigenbasisPartitionFunction (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑' i, eigenbasisBoltzmannWeight E β i

/-- Absolute Boltzmann summability implies ordinary summability of the positive weights. -/
theorem eigenbasisBoltzmannWeight_summable (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    Summable (eigenbasisBoltzmannWeight E β) :=
  Summable.of_norm hsum

/-- For a nonempty energy index, a summable family of strictly positive Boltzmann weights
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

/-- The normalized Gibbs probability of an energy level. -/
noncomputable def eigenbasisGibbsProbability (E : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  (eigenbasisPartitionFunction E β)⁻¹ * eigenbasisBoltzmannWeight E β i


/-- The normalized Gibbs distribution is insensitive to a common energy
offset whenever the Boltzmann weights are defined. -/
theorem eigenbasisGibbsProbability_add_const (E : ι → ℝ) (β c : ℝ) (i : ι) :
    eigenbasisGibbsProbability (fun j => E j + c) β i =
      eigenbasisGibbsProbability E β i := by
  change Real.normalizedWeight
      (eigenbasisBoltzmannWeight (fun j => E j + c) β) i =
    Real.normalizedWeight (eigenbasisBoltzmannWeight E β) i
  have hweights :
      eigenbasisBoltzmannWeight (fun j => E j + c) β =
        (fun j => Real.exp (-β * c) * eigenbasisBoltzmannWeight E β j) := by
    funext j
    exact eigenbasisBoltzmannWeight_add_const E β c j
  rw [hweights]
  exact Real.normalizedWeight_mul_left _ _ (Real.exp_pos _).ne' i


theorem eigenbasisGibbsProbability_nonneg (E : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ eigenbasisGibbsProbability E β i := by
  unfold eigenbasisGibbsProbability
  exact mul_nonneg
    (inv_nonneg.mpr (by
      rw [eigenbasisPartitionFunction]
      exact tsum_nonneg fun j => eigenbasisBoltzmannWeight_nonneg E β j))
    (eigenbasisBoltzmannWeight_nonneg E β i)

/-- The normalized Gibbs probabilities sum to one. -/
theorem hasSum_eigenbasisGibbsProbability [Nonempty ι] (E : ι → ℝ) (β : ℝ)
    (hsum : EigenbasisGibbsSummable E β) :
    HasSum (eigenbasisGibbsProbability E β) 1 := by
  exact
    Real.hasSum_normalizedWeight (eigenbasisBoltzmannWeight E β)
      (eigenbasisBoltzmannWeight_summable E β hsum)
      (eigenbasisPartitionFunction_pos E β hsum).ne'

/-- Absolute integrability of energy with respect to the Gibbs probabilities. Existence of the
normalized probabilities alone does not imply finite mean energy. -/
def EigenbasisGibbsEnergyIntegrable (E : ι → ℝ) (β : ℝ) : Prop :=
  Summable fun i => ‖eigenbasisGibbsProbability E β i * E i‖

/-- On a finite energy index, the Boltzmann summability hypothesis is automatic. -/
theorem eigenbasisGibbsSummable_of_finite [Finite ι] (E : ι → ℝ) (β : ℝ) :
    EigenbasisGibbsSummable E β := by
  exact Summable.of_finite

end QuantumTheory
