import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalFullFock
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula

set_option linter.style.header false

/-!
# Compatibility of canonical Gibbs states on a sector and on full Fock space

The full-Fock canonical density is the isometric zero extension of its fixed-number
sector representative, not an independent thermal state. In particular, this
identification does not assume that individual field operators preserve particle number.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

private theorem canonicalPullback_basisState_of_sector (N : ℕ)
    (n : ParticleNumberSector Mode Config N) :
    completedCoordinatePullback
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      Subtype.val_injective (completedBasisState n.val) = completedBasisState n := by
  classical
  ext m
  rw [completedCoordinatePullback_apply]
  by_cases h : m = n
  · subst m
    simp
  · have hv : (m : Config) ≠ n.val := fun he => h (Subtype.ext he)
    simp [completedBasisState_apply_of_ne hv, completedBasisState_apply_of_ne h]

private theorem canonicalPullback_basisState_of_ne (N : ℕ)
    (c : Config) (hc : particleNumber (Mode := Mode) c ≠ N) :
    completedCoordinatePullback
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      Subtype.val_injective (completedBasisState c) = 0 := by
  classical
  ext n
  rw [completedCoordinatePullback_apply]
  have hv : (n : Config) ≠ c := by
    intro he
    apply hc
    rw [← he]
    exact n.property
  simp [completedBasisState_apply_of_ne hv]

/-- The canonical density on the full completed Fock space is the zero extension
of the Gibbs density on its fixed-number sector, as a bounded operator.
The inclusion is an isometry and pullback is its Hilbert adjoint. -/
theorem canonicalFullGibbsDensityOperator_eq_sector_embedding
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).op =
      (completedCoordinateEmbedding
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective).toContinuousLinearMap.comp
        ((canonicalGibbsDensityOperator (Config := Config) ε β N hsum).op.comp
          (completedCoordinatePullback
            (Subtype.val : ParticleNumberSector Mode Config N → Config)
            Subtype.val_injective)) := by
  classical
  apply continuousLinearMap_ext_completedBasis
  intro c
  by_cases hc : particleNumber (Mode := Mode) c = N
  · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
    change
      (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).op
          (completedBasisState n.val) =
        (completedCoordinateEmbedding
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective).toContinuousLinearMap
          ((canonicalGibbsDensityOperator (Config := Config) ε β N hsum).op
            (completedCoordinatePullback
              (Subtype.val : ParticleNumberSector Mode Config N → Config)
              Subtype.val_injective (completedBasisState n.val)))
    rw [canonicalFullGibbsDensityOperator_apply_basis_of_sector,
      canonicalPullback_basisState_of_sector,
      canonicalGibbsDensityOperator_apply_basis, map_smul]
    exact (congrArg
      (fun ψ : CompletedFock Config =>
        (eigenbasisGibbsProbability
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n : ℂ) • ψ)
      (completedCoordinateEmbedding_basisState
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective n)).symm
  · change
      (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).op
          (completedBasisState c) =
        (completedCoordinateEmbedding
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective).toContinuousLinearMap
          ((canonicalGibbsDensityOperator (Config := Config) ε β N hsum).op
            (completedCoordinatePullback
              (Subtype.val : ParticleNumberSector Mode Config N → Config)
              Subtype.val_injective (completedBasisState c)))
    rw [canonicalFullGibbsDensityOperator_apply_basis_of_ne ε β N hsum c hc,
      canonicalPullback_basisState_of_ne N c hc]
    simp


/-- The fixed-number canonical state on the full completed Fock space is
invariant under a common one-particle energy offset. The proof transports
the sector result through the actual zero-extension representation. -/
theorem canonicalFullGibbsDensityOperator_shift_invariant
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) (C : ℝ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    canonicalFullGibbsDensityOperator (Config := Config)
        (fun i => ε i + C) β N
        (canonicalGibbsSummable_shift ε β N C hsum) =
      canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum := by
  apply DensityOperator.ext
  rw [canonicalFullGibbsDensityOperator_eq_sector_embedding,
    canonicalFullGibbsDensityOperator_eq_sector_embedding,
    canonicalGibbsDensityOperator_shift_invariant]


/-- Restricting a bounded full-Fock operator to the sharp-number sector preserves
its diagonal matrix elements on the embedded occupation basis. This does not
require the operator to preserve particle number. -/
private theorem canonicalCompressedDiagonalMatrixElement (N : ℕ)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config)
    (n : ParticleNumberSector Mode Config N) :
    inner ℂ (completedBasisState n)
      (((completedCoordinatePullback
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective).comp
        (A.comp
          (completedCoordinateEmbedding
            (Subtype.val : ParticleNumberSector Mode Config N → Config)
            Subtype.val_injective).toContinuousLinearMap))
        (completedBasisState n)) =
    inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_completedBasisState_left, completedCoordinatePullback_apply]
  change
    (A (completedCoordinateEmbedding
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      Subtype.val_injective (completedBasisState n))) n.val =
      inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))
  rw [completedCoordinateEmbedding_basisState, inner_completedBasisState_left]

/-- A bounded full-Fock observable has the same canonical expectation as its
compression to the fixed-number sector. The ambient operator may connect
different particle-number sectors; only the final expectation is restricted. -/
theorem canonicalFullGibbsDensityOperator_expectation_eq_sector
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).expectation A =
      (canonicalGibbsDensityOperator (Config := Config) ε β N hsum).expectation
        ((completedCoordinatePullback
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective).comp
          (A.comp
            (completedCoordinateEmbedding
              (Subtype.val : ParticleNumberSector Mode Config N → Config)
              Subtype.val_injective).toContinuousLinearMap)) := by
  classical
  let E : ParticleNumberSector Mode Config N → ℝ := fun n => occupationEnergy ε n.val
  let B : CompletedFock (ParticleNumberSector Mode Config N) →L[ℂ]
      CompletedFock (ParticleNumberSector Mode Config N) :=
    (completedCoordinatePullback
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      Subtype.val_injective).comp
      (A.comp
        (completedCoordinateEmbedding
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective).toContinuousLinearMap)
  let f : ParticleNumberSector Mode Config N → ℂ := fun n =>
    (eigenbasisGibbsProbability E β n : ℂ) *
      inner ℂ (completedBasisState n) (B (completedBasisState n))
  let g : Config → ℂ := fun c =>
    (Real.normalizedWeight (canonicalFullGibbsWeight ε β N) c : ℂ) *
      inner ℂ (completedBasisState c) (A (completedBasisState c))
  have hSector : HasSum f
      ((canonicalGibbsDensityOperator (Config := Config) ε β N hsum).expectation B) := by
    simpa only [f, E, completedHilbertBasis_apply] using
      (canonicalGibbsDensityOperator (Config := Config) ε β N hsum).hasSum_expectation_diagonal
        B (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
        (eigenbasisGibbsProbability E β)
        (fun n => by
          simpa only [E, completedHilbertBasis_apply] using
            (canonicalGibbsDensityOperator_apply_basis ε β N hsum n))
  have hFull : HasSum g
      ((canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).expectation A) := by
    simpa only [g, completedHilbertBasis_apply] using
      (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).hasSum_expectation_diagonal
        A (completedHilbertBasis (Config := Config))
        (Real.normalizedWeight (canonicalFullGibbsWeight ε β N))
        (fun c => by
          simpa only [canonicalFullGibbsDensityOperator, completedHilbertBasis_apply] using
            (diagonalDensityOperator_apply_basis
              (completedHilbertBasis (Config := Config))
              (canonicalFullGibbsWeight ε β N)
              (canonicalFullGibbsWeight_norm_summable ε β N hsum)
              (canonicalFullGibbsWeight_nonneg ε β N)
              (canonicalFullGibbsWeight_tsum_pos ε β N hsum) c))
  have hPoint :
      Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 = g := by
    funext c
    by_cases hc : particleNumber (Mode := Mode) c = N
    · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 n.val = g n.val
      rw [Subtype.val_injective.extend_apply]
      change (eigenbasisGibbsProbability E β n : ℂ) *
          inner ℂ (completedBasisState n) (B (completedBasisState n)) =
        (Real.normalizedWeight (canonicalFullGibbsWeight ε β N) n.val : ℂ) *
          inner ℂ (completedBasisState n.val) (A (completedBasisState n.val))
      rw [normalizedWeight_canonicalFullGibbsWeight_apply_sector ε β N hsum n]
      exact congrArg (fun z : ℂ => (eigenbasisGibbsProbability E β n : ℂ) * z)
        (canonicalCompressedDiagonalMatrixElement N A n)
    · have hnot : ¬ ∃ n : ParticleNumberSector Mode Config N, n.val = c := by
        rintro ⟨n, hn⟩
        apply hc
        rw [← hn]
        exact n.property
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 c = g c
      rw [Function.extend_apply' _ _ _ hnot]
      simp [g, Real.normalizedWeight,
        canonicalFullGibbsWeight_apply_of_ne ε β N c hc]
  have hExtended : HasSum
      (Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0)
      ((canonicalGibbsDensityOperator (Config := Config) ε β N hsum).expectation B) :=
    (hasSum_extend_zero Subtype.val_injective).2 hSector
  rw [hPoint] at hExtended
  change
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).expectation A =
      (canonicalGibbsDensityOperator (Config := Config) ε β N hsum).expectation B
  exact hFull.unique hExtended

end

end Common
end SecondQuantization
