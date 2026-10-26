import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.GrandCanonicalSectorDecomposition

set_option linter.style.header false

/-!
# Density-operator compatibility of canonical and grand-canonical Gibbs states

The scalar sector weights, summability, probabilities, and partition-function
decomposition are owned by GrandCanonicalSectorDecomposition. This module
uses those scalar identities to identify the sharp-number compression of the
full-Fock grand-canonical Gibbs density with the zero-extended canonical density
scaled by the sector probability.

The equality holds on the completed occupation Fock space without a finite-mode
assumption or CCR/CAR. The compressed operator need not have trace one.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

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
      completedCoordinateProjection_basisState]
    simp only [hc, ↓reduceIte]
    rw [grandCanonicalGibbsDensityOperator_apply_basis, map_smul,
      completedCoordinateProjection_basisState]
    simp only [hc, ↓reduceIte]
    rw [smul_apply]
    change
      (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) •
        completedBasisState n.val =
      (grandCanonicalSectorProbability ε β μ N : ℂ) •
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).op
          (completedBasisState n.val)
    rw [canonicalFullGibbsDensityOperator_apply_basis_of_sector, smul_smul]
    simpa only [Complex.ofReal_mul] using
      congrArg (fun z : ℝ => (z : ℂ) • completedBasisState n.val)
        (grandCanonicalGibbsProbability_of_sector ε β μ N hsum n)
  · simp [ContinuousLinearMap.comp_apply, completedCoordinateProjection_basisState,
      hc, canonicalFullGibbsDensityOperator_apply_basis_of_ne ε β N
        (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum) c hc]

/-- The expectation of any bounded full-Fock observable in a summable grand-canonical
Gibbs state is an absolutely convergent sum over sharp-number sectors.
The sector summands are unnormalized, so this includes empty sectors without a
nonemptiness or canonical Gibbs-state hypothesis. -/
theorem grandCanonicalGibbsDensityOperator_expectation_eq_tsum_sector
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).expectation A =
      ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N,
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) *
          inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) := by
  let ρ := grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum
  let f : Config → ℂ := fun c =>
    (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c : ℂ) *
      inner ℂ (completedBasisState c) (A (completedBasisState c))
  have hdiag : ∀ c : Config,
      ρ.op ((completedHilbertBasis (Config := Config)) c) =
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β c : ℂ) •
          (completedHilbertBasis (Config := Config)) c := by
    intro c
    simpa only [ρ, completedHilbertBasis_apply] using
      (grandCanonicalGibbsDensityOperator_apply_basis ε β μ hsum c)
  have hfull : HasSum f (ρ.expectation A) := by
    simpa only [f, completedHilbertBasis_apply] using
      (ρ.hasSum_expectation_diagonal A
        (completedHilbertBasis (Config := Config))
        (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β) hdiag)
  change ρ.expectation A =
    ∑' N : ℕ, ∑' n : ParticleNumberSector Mode Config N, f n.val
  exact (hfull.tsum_fiberwise
    (particleNumber (Mode := Mode) (Config := Config))).tsum_eq.symm

/-- On a nonempty sharp-number sector, the unnormalized contribution to any
bounded grand-canonical expectation equals its probability times the
expectation in the fixed-number canonical state, zero-extended to full Fock. -/
theorem grandCanonicalGibbsDensityOperator_sector_expectation_eq_canonical
    (ε : Mode → ℝ) (β μ : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (∑' n : ParticleNumberSector Mode Config N,
      (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) *
        inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))) =
      (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) *
        (canonicalFullGibbsDensityOperator (Config := Config) ε β N
          (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).expectation A := by
  classical
  let hcan := canonicalGibbsSummable_of_grandCanonical ε β μ N hsum
  let ρ := canonicalGibbsDensityOperator (Config := Config) ε β N hcan
  let U := (completedCoordinateEmbedding
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    Subtype.val_injective).toContinuousLinearMap
  let V := completedCoordinatePullback
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    Subtype.val_injective
  let B := V.comp (A.comp U)
  let E : ParticleNumberSector Mode Config N → ℝ := fun n => occupationEnergy ε n.val
  have hcompress (n : ParticleNumberSector Mode Config N) :
      inner ℂ (completedBasisState n) (B (completedBasisState n)) =
        inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) := by
    have hU : U (completedBasisState n) = completedBasisState n.val := by
      change completedCoordinateEmbedding
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective (completedBasisState n) = completedBasisState n.val
      exact completedCoordinateEmbedding_basisState _ _ n
    simp only [B, V, ContinuousLinearMap.comp_apply,
      inner_completedBasisState_left, completedCoordinatePullback_apply, hU]
  have hdiag : ∀ n : ParticleNumberSector Mode Config N,
      ρ.op ((completedHilbertBasis (Config := ParticleNumberSector Mode Config N)) n) =
        (eigenbasisGibbsProbability E β n : ℂ) •
          (completedHilbertBasis (Config := ParticleNumberSector Mode Config N)) n := by
    intro n
    simpa only [ρ, E, completedHilbertBasis_apply] using
      (canonicalGibbsDensityOperator_apply_basis ε β N hcan n)
  have hsector :
      ρ.expectation B =
        ∑' n : ParticleNumberSector Mode Config N,
          (eigenbasisGibbsProbability E β n : ℂ) *
            inner ℂ (completedBasisState n) (B (completedBasisState n)) := by
    simpa only [completedHilbertBasis_apply] using
      (ρ.expectation_eq_tsum_diagonal B
        (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
        (eigenbasisGibbsProbability E β) hdiag)
  calc
    (∑' n : ParticleNumberSector Mode Config N,
      (eigenbasisGibbsProbability (grandCanonicalEnergy ε μ) β n.val : ℂ) *
        inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))) =
        (grandCanonicalSectorProbability ε β μ N : ℂ) *
          ∑' n : ParticleNumberSector Mode Config N,
            (eigenbasisGibbsProbability E β n : ℂ) *
              inner ℂ (completedBasisState n) (B (completedBasisState n)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [hcompress n]
      simpa only [Complex.ofReal_mul, mul_assoc] using
        congrArg
          (fun w : ℝ => (w : ℂ) *
            inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)))
          (grandCanonicalGibbsProbability_of_sector ε β μ N hsum n)
    _ = (grandCanonicalSectorProbability ε β μ N : ℂ) * ρ.expectation B := by
      rw [hsector]
    _ = _ := by
      congr 1
      exact (canonicalFullGibbsDensityOperator_expectation_eq_sector
        ε β N hcan A).symm

open Classical in
/-- Every bounded grand-canonical expectation is a probability-weighted mixture
of full-Fock canonical expectations. Empty particle-number sectors contribute zero;
no particle-number conservation assumption is imposed on the observable. -/
theorem grandCanonicalGibbsDensityOperator_expectation_eq_tsum_canonical
    (ε : Mode → ℝ) (β μ : ℝ)
    (hsum : EigenbasisGibbsSummable
      (grandCanonicalEnergy (Config := Config) ε μ) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (grandCanonicalGibbsDensityOperator (Config := Config) ε β μ hsum).expectation A =
      ∑' N : ℕ,
        if hN : Nonempty (ParticleNumberSector Mode Config N) then
          letI : Nonempty (ParticleNumberSector Mode Config N) := hN
          (grandCanonicalSectorProbability (Config := Config) ε β μ N : ℂ) *
            (canonicalFullGibbsDensityOperator (Config := Config) ε β N
              (canonicalGibbsSummable_of_grandCanonical ε β μ N hsum)).expectation A
        else 0 := by
  classical
  rw [grandCanonicalGibbsDensityOperator_expectation_eq_tsum_sector ε β μ hsum A]
  apply tsum_congr
  intro N
  by_cases hN : Nonempty (ParticleNumberSector Mode Config N)
  · letI : Nonempty (ParticleNumberSector Mode Config N) := hN
    simpa only [dite_eq_left hN] using
      (grandCanonicalGibbsDensityOperator_sector_expectation_eq_canonical
        ε β μ N hsum A)
  · letI : IsEmpty (ParticleNumberSector Mode Config N) :=
      ⟨fun n => hN ⟨n⟩⟩
    simp only [dite_eq_right hN]
    simp

end

end Common
end SecondQuantization
