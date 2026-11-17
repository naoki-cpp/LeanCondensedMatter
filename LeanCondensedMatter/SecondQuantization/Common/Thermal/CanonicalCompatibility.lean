import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateIsometry
import LeanCondensedMatter.SecondQuantization.Common.Thermal.CanonicalFullFock

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
      completedCoordinatePullback_basisState_of_image,
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
    have hnot : c ∉ Set.range
        (Subtype.val : ParticleNumberSector Mode Config N → Config) := by
      rintro ⟨n, hn⟩
      apply hc
      rw [← hn]
      exact n.property
    rw [canonicalFullGibbsDensityOperator_apply_basis_of_ne ε β N hsum c hc,
      completedCoordinatePullback_basisState_of_not_mem
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective c hnot]
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


/-- A full-Fock canonical Gibbs expectation is its absolutely convergent
occupation-diagonal series over the fixed-particle-number sector, even when
the bounded observable does not preserve that sector. -/
theorem canonicalFullGibbsDensityOperator_expectation_eq_tsum_sector
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (A : CompletedFock Config →L[ℂ] CompletedFock Config) :
    (canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum).expectation A =
      ∑' n : ParticleNumberSector Mode Config N,
        (eigenbasisGibbsProbability
          (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n : ℂ) *
          inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) := by
  classical
  let ρ := canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum
  let w : Config → ℝ := Real.normalizedWeight (canonicalFullGibbsWeight ε β N)
  let g : Config → ℂ := fun c =>
    (w c : ℂ) * inner ℂ (completedBasisState c) (A (completedBasisState c))
  have hdiag : ∀ c : Config,
      ρ.op ((completedHilbertBasis (Config := Config)) c) =
        (w c : ℂ) • (completedHilbertBasis (Config := Config)) c := by
    intro c
    simpa only [ρ, canonicalFullGibbsDensityOperator, w, completedHilbertBasis_apply] using
      (diagonalDensityOperator_apply_basis
        (completedHilbertBasis (Config := Config)) (canonicalFullGibbsWeight ε β N)
        (canonicalFullGibbsWeight_norm_summable ε β N hsum)
        (canonicalFullGibbsWeight_nonneg ε β N)
        (canonicalFullGibbsWeight_tsum_pos ε β N hsum) c)
  have hfull : HasSum g (ρ.expectation A) := by
    simpa only [g, completedHilbertBasis_apply] using
      (ρ.hasSum_expectation_diagonal A
        (completedHilbertBasis (Config := Config)) w hdiag)
  have hindicator :
      HasSum
        (({c : Config | particleNumber (Mode := Mode) c = N} : Set Config).indicator g)
        (ρ.expectation A) := by
    apply hfull.congr_fun
    intro c
    by_cases hc : particleNumber (Mode := Mode) c = N
    · simp [Set.indicator, hc]
    · simp [Set.indicator, hc, g, w, Real.normalizedWeight,
        canonicalFullGibbsWeight_apply_of_ne ε β N c hc]
  have hsector :
      HasSum (fun n : ParticleNumberSector Mode Config N => g n.val) (ρ.expectation A) :=
    (hasSum_subtype_iff_indicator
      (s := {c : Config | particleNumber (Mode := Mode) c = N}) (f := g)).2 hindicator
  calc
    ρ.expectation A = ∑' n : ParticleNumberSector Mode Config N, g n.val :=
      hsector.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [g, w, normalizedWeight_canonicalFullGibbsWeight_apply_sector ε β N hsum n]

/-- A bounded full-Fock observable has the same canonical expectation as its
compression to the fixed-number sector. The observable need not preserve
particle number; the density is zero outside its sector. -/
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
  let ρ := canonicalGibbsDensityOperator (Config := Config) ε β N hsum
  let B := (completedCoordinatePullback
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    Subtype.val_injective).comp
    (A.comp
      (completedCoordinateEmbedding
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective).toContinuousLinearMap)
  let E : ParticleNumberSector Mode Config N → ℝ := fun n => occupationEnergy ε n.val
  have hdiag : ∀ n : ParticleNumberSector Mode Config N,
      ρ.op ((completedHilbertBasis (Config := ParticleNumberSector Mode Config N)) n) =
        (eigenbasisGibbsProbability E β n : ℂ) •
          (completedHilbertBasis (Config := ParticleNumberSector Mode Config N)) n := by
    intro n
    simpa only [ρ, E, completedHilbertBasis_apply] using
      (canonicalGibbsDensityOperator_apply_basis ε β N hsum n)
  rw [canonicalFullGibbsDensityOperator_expectation_eq_tsum_sector ε β N hsum A]
  change _ = ρ.expectation B
  rw [ρ.expectation_eq_tsum_diagonal B
    (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
    (eigenbasisGibbsProbability E β) hdiag]
  apply tsum_congr
  intro n
  change
    (eigenbasisGibbsProbability E β n : ℂ) *
      inner ℂ (completedBasisState n.val) (A (completedBasisState n.val)) =
    (eigenbasisGibbsProbability E β n : ℂ) *
      inner ℂ (completedBasisState n) (B (completedBasisState n))
  exact congrArg (fun z : ℂ => (eigenbasisGibbsProbability E β n : ℂ) * z)
    (by simpa only [B] using
      (inner_completedBasisState_coordinatePullback_comp
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective A n).symm)

end

end Common
end SecondQuantization
