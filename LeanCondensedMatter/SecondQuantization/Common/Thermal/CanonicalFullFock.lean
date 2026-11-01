import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalSector

set_option linter.style.header false

/-!
# Canonical Gibbs density on the full completed Fock space

A fixed-number canonical density can be represented on the full Fock space by
extending its positive Boltzmann weights by zero outside the chosen sector.
This keeps the full algebra of creation and annihilation operators available.

The construction reuses the common diagonal density operator. Its partition sum
equals the sharp-number sector partition function, and its diagonal probabilities
agree with the sector Gibbs state. No Wick or unrestricted KMS property is assumed.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- Unnormalized canonical Boltzmann weights on the full occupation Fock basis:
zero outside the sector with total particle number `N`. -/
noncomputable def canonicalFullGibbsWeight (ε : Mode → ℝ) (β : ℝ) (N : ℕ) :
    Config → ℝ :=
  Function.extend
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    (fun n : ParticleNumberSector Mode Config N =>
      eigenbasisBoltzmannWeight
        (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n) 0

/-- Extending the restricted weights by zero preserves their partition sum. -/
theorem canonicalFullGibbsWeight_hasSum (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    HasSum (canonicalFullGibbsWeight (Config := Config) ε β N)
      (canonicalPartitionFunction (Config := Config) ε β N) := by
  unfold canonicalFullGibbsWeight canonicalPartitionFunction eigenbasisPartitionFunction
  exact (hasSum_extend_zero Subtype.val_injective).2
    (eigenbasisBoltzmannWeight_summable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β hsum).hasSum

/-- On the chosen sector the extended weight equals the original Boltzmann weight. -/
@[simp]
theorem canonicalFullGibbsWeight_apply_sector (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (n : ParticleNumberSector Mode Config N) :
    canonicalFullGibbsWeight (Config := Config) ε β N n.val =
      eigenbasisBoltzmannWeight
        (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  simp only [canonicalFullGibbsWeight, Subtype.val_injective.extend_apply]

/-- Outside the prescribed sector the canonical weight vanishes. -/
theorem canonicalFullGibbsWeight_apply_of_ne (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (c : Config) (hc : particleNumber (Mode := Mode) c ≠ N) :
    canonicalFullGibbsWeight (Config := Config) ε β N c = 0 := by
  have hnot : ¬ ∃ n : ParticleNumberSector Mode Config N, n.val = c := by
    rintro ⟨n, hn⟩
    apply hc
    rw [← hn]
    exact n.property
  unfold canonicalFullGibbsWeight
  rw [Function.extend_apply' _ _ _ hnot]
  simp

/-- The full-space canonical Boltzmann weights are nonnegative. -/
theorem canonicalFullGibbsWeight_nonneg (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (c : Config) : 0 ≤ canonicalFullGibbsWeight (Config := Config) ε β N c := by
  by_cases hc : particleNumber (Mode := Mode) c = N
  · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
    rw [show c = n.val from rfl, canonicalFullGibbsWeight_apply_sector]
    exact eigenbasisBoltzmannWeight_nonneg _ _ n
  · rw [canonicalFullGibbsWeight_apply_of_ne ε β N c hc]

/-- Sector Boltzmann summability implies absolute summability of its zero extension. -/
theorem canonicalFullGibbsWeight_norm_summable (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    Summable (fun c : Config => ‖canonicalFullGibbsWeight (Config := Config) ε β N c‖) :=
  (canonicalFullGibbsWeight_hasSum ε β N hsum).summable.norm

/-- A nonempty sharp-number sector gives positive full-space partition normalization. -/
theorem canonicalFullGibbsWeight_tsum_pos (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    0 < ∑' c : Config, canonicalFullGibbsWeight ε β N c := by
  rw [(canonicalFullGibbsWeight_hasSum ε β N hsum).tsum_eq]
  exact canonicalPartitionFunction_pos ε β N hsum

/-- Normalizing the zero-extended fixed-number Boltzmann weights agrees
with the Gibbs probability computed directly on the sector. -/
theorem normalizedWeight_canonicalFullGibbsWeight_apply_sector
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (n : ParticleNumberSector Mode Config N) :
    Real.normalizedWeight (canonicalFullGibbsWeight ε β N) n.val =
      eigenbasisGibbsProbability
        (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  unfold Real.normalizedWeight eigenbasisGibbsProbability
  rw [(canonicalFullGibbsWeight_hasSum ε β N hsum).tsum_eq,
    canonicalPartitionFunction, canonicalFullGibbsWeight_apply_sector]

/-- The canonical Gibbs density on the entire completed Fock space, supported
exactly on occupation configurations with particle number `N`. -/
noncomputable def canonicalFullGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    DensityOperator (CompletedFock Config) :=
  diagonalDensityOperator (completedHilbertBasis (Config := Config))
    (canonicalFullGibbsWeight ε β N)
    (canonicalFullGibbsWeight_norm_summable ε β N hsum)
    (canonicalFullGibbsWeight_nonneg ε β N)
    (canonicalFullGibbsWeight_tsum_pos ε β N hsum)

/-- The full-Fock canonical state has the same diagonal occupation probabilities
as the fixed-number sector state on every admitted configuration. -/
theorem canonicalFullGibbsDensityOperator_apply_basis_of_sector
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (n : ParticleNumberSector Mode Config N) :
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).op
        (completedBasisState n.val) =
      (eigenbasisGibbsProbability
        (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n : ℂ) •
        completedBasisState n.val := by
  simpa only [canonicalFullGibbsDensityOperator, completedHilbertBasis_apply,
    normalizedWeight_canonicalFullGibbsWeight_apply_sector ε β N hsum n] using
    (diagonalDensityOperator_apply_basis
      (completedHilbertBasis (Config := Config)) (canonicalFullGibbsWeight ε β N)
      (canonicalFullGibbsWeight_norm_summable ε β N hsum)
      (canonicalFullGibbsWeight_nonneg ε β N)
      (canonicalFullGibbsWeight_tsum_pos ε β N hsum) n.val)

/-- The canonical density annihilates basis states in all other particle-number sectors. -/
theorem canonicalFullGibbsDensityOperator_apply_basis_of_ne
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (c : Config) (hc : particleNumber (Mode := Mode) c ≠ N) :
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).op
        (completedBasisState c) = 0 := by
  have hzero : Real.normalizedWeight (canonicalFullGibbsWeight ε β N) c = 0 := by
    simp [Real.normalizedWeight, canonicalFullGibbsWeight_apply_of_ne ε β N c hc]
  simpa [canonicalFullGibbsDensityOperator, completedHilbertBasis_apply, hzero] using
    (diagonalDensityOperator_apply_basis
      (completedHilbertBasis (Config := Config)) (canonicalFullGibbsWeight ε β N)
      (canonicalFullGibbsWeight_norm_summable ε β N hsum)
      (canonicalFullGibbsWeight_nonneg ε β N)
      (canonicalFullGibbsWeight_tsum_pos ε β N hsum) c)

end

end Common
end SecondQuantization
