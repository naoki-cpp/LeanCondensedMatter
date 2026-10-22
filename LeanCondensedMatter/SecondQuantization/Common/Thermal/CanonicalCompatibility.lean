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

end

end Common
end SecondQuantization
