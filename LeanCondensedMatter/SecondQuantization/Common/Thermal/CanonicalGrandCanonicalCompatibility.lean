import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonical

set_option linter.style.header false

/-!
# Conditioning a grand-canonical Gibbs state on particle number

A full-Fock grand-canonical Gibbs state, when its Boltzmann weights are summable,
restricts to summable weights on every sharp-particle-number sector. On a nonempty
sector, the unnormalized restriction of the grand-canonical density is its
canonical Gibbs density multiplied by the sector probability

  exp(β μ N) Z_N / Ξ.

The operator-level formula holds on the completed occupation Fock space without
assuming finitely many modes, bounded energy, or bosonic/fermionic CCR/CAR.
The projected operator is generally not itself a density operator: its trace
is the probability of the sector, not one.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- Summability of the full grand-canonical Gibbs weights implies summability
of their restriction to every fixed-number sector. This includes sectors with
infinitely many configurations, and requires no nonemptiness hypothesis. -/
theorem canonicalGibbsSummable_of_grandCanonical
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β := by
  have hrestricted : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N =>
        grandCanonicalEnergy ε μ n.val) β :=
    hsum.comp_injective Subtype.val_injective
  have hE :
      (fun n : ParticleNumberSector Mode Config N =>
        grandCanonicalEnergy ε μ n.val) =
      (fun n : ParticleNumberSector Mode Config N =>
        occupationEnergy ε n.val - μ * (N : ℝ)) := by
    funext n
    simp [grandCanonicalEnergy, n.property]
  rw [hE] at hrestricted
  simpa only [sub_add_cancel] using
    (eigenbasisGibbsSummable_add_const
      (fun n : ParticleNumberSector Mode Config N =>
        occupationEnergy ε n.val - μ * (N : ℝ))
      β (μ * (N : ℝ)) hrestricted)

/-- Within a fixed-number sector the chemical-potential correction is a
constant fugacity factor multiplying the canonical Boltzmann weight. -/
theorem grandCanonicalBoltzmannWeight_of_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    (n : ParticleNumberSector Mode Config N) :
    eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val =
      Real.exp (β * μ * (N : ℝ)) *
        eigenbasisBoltzmannWeight
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  change Real.exp
      (-β * (occupationEnergy ε n.val -
        μ * (particleNumber (Mode := Mode) n.val : ℝ))) =
    Real.exp (β * μ * (N : ℝ)) * Real.exp (-β * occupationEnergy ε n.val)
  rw [n.property]
  rw [show -β * (occupationEnergy ε n.val - μ * (N : ℝ)) =
      β * μ * (N : ℝ) + -β * occupationEnergy ε n.val by ring,
    Real.exp_add]

/-- Probability assigned by the grand-canonical distribution to the
fixed-particle-number sector. It can be zero when the sector is empty. -/
noncomputable def grandCanonicalSectorProbability
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ) : ℝ :=
  Real.exp (β * μ * (N : ℝ)) *
    canonicalPartitionFunction (Config := Config) ε β N /
      grandCanonicalPartitionFunction (Config := Config) ε β μ

/-- Conditioning the grand-canonical occupation probability on a nonempty
sharp-number sector gives its canonical Gibbs occupation probability. -/
theorem grandCanonicalGibbsProbability_of_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (n : ParticleNumberSector Mode Config N) :
    eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val =
      grandCanonicalSectorProbability (Config := Config) ε β μ N *
        eigenbasisGibbsProbability
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n := by
  have hZ : grandCanonicalPartitionFunction (Config := Config) ε β μ ≠ 0 :=
    (grandCanonicalPartitionFunction_pos ε β μ hsum).ne'
  have hZN : canonicalPartitionFunction (Config := Config) ε β N ≠ 0 :=
    (canonicalPartitionFunction_pos ε β N
      (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).ne'
  change (grandCanonicalPartitionFunction ε β μ)⁻¹ *
      eigenbasisBoltzmannWeight (grandCanonicalEnergy ε μ) β n.val =
    (Real.exp (β * μ * (N : ℝ)) *
      canonicalPartitionFunction ε β N /
      grandCanonicalPartitionFunction ε β μ) *
      ((canonicalPartitionFunction ε β N)⁻¹ *
        eigenbasisBoltzmannWeight
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n)
  rw [grandCanonicalBoltzmannWeight_of_sector]
  field_simp [hZ, hZN]
  ring

/-- A particle-number compression of the grand-canonical density equals the
full-Fock zero extension of the canonical density scaled by the probability
of that sector. These are equalities of bounded operators, not of normalized
density operators. No number-conservation condition on an observable is needed. -/
theorem grandCanonicalGibbsDensityOperator_compress_sector
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β) :
    (completedCoordinateProjection
        (fun c : Config => particleNumber (Mode := Mode) c = N)).comp
      ((grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).op.comp
        (completedCoordinateProjection
          (fun c : Config => particleNumber (Mode := Mode) c = N))) =
      (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) •
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op := by
  classical
  apply continuousLinearMap_ext_completedBasis
  intro c
  by_cases hc : particleNumber (Mode := Mode) c = N
  · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      completedCoordinateProjection_basisState, if_pos hc]
    rw [grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedCoordinateProjection_basisState, if_pos hc]
    rw [smul_apply, canonicalFullGibbsDensityOperator_apply_basis_of_sector,
      smul_smul]
    simpa only [Complex.ofReal_mul] using
      congrArg (fun z : ℝ => (z : ℂ) • completedBasisState n.val)
        (grandCanonicalGibbsProbability_of_sector ε β μ N hsum n)
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      completedCoordinateProjection_basisState, if_neg hc]
    simp [canonicalFullGibbsDensityOperator_apply_basis_of_ne ε β N
      (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum) c hc]

end

end Common
end SecondQuantization
