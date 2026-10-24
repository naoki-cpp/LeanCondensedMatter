import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateIsometry
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


/-- A bounded full-Fock observable has the same canonical expectation as its
compression to the fixed-number sector. The ambient operator may connect
different particle-number sectors; only the final expectation is restricted.
The proof uses the zero-extension operator identity and trace-class diagonal
series, without separately expanding Gibbs normalization. -/
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
  let ρF := canonicalFullGibbsDensityOperator (Config := Config) ε β N hsum
  let ρN := canonicalGibbsDensityOperator (Config := Config) ε β N hsum
  let U := (completedCoordinateEmbedding
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    Subtype.val_injective).toContinuousLinearMap
  let V := completedCoordinatePullback
    (Subtype.val : ParticleNumberSector Mode Config N → Config)
    Subtype.val_injective
  let B := V.comp (A.comp U)
  have hop : ρF.op = U.comp (ρN.op.comp V) := by
    simpa only [ρF, ρN, U, V] using
      (canonicalFullGibbsDensityOperator_eq_sector_embedding ε β N hsum)
  let f : ParticleNumberSector Mode Config N → ℂ := fun n =>
    inner ℂ (completedBasisState n) ((ρN.op * B) (completedBasisState n))
  let g : Config → ℂ := fun c =>
    inner ℂ (completedBasisState c) ((ρF.op * A) (completedBasisState c))
  have hSector : HasSum f (ρN.expectation B) := by
    rw [ρN.expectation_apply]
    simpa only [f, completedHilbertBasis_apply, mul_apply_eq_comp] using
      (ρN.isTraceClass.comp_right B).hasSum_trace
        (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
  have hFull : HasSum g (ρF.expectation A) := by
    rw [ρF.expectation_apply]
    simpa only [g, completedHilbertBasis_apply, mul_apply_eq_comp] using
      (ρF.isTraceClass.comp_right A).hasSum_trace
        (completedHilbertBasis (Config := Config))
  have hPoint :
      Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 = g := by
    funext c
    by_cases hc : particleNumber (Mode := Mode) c = N
    · let n : ParticleNumberSector Mode Config N := ⟨c, hc⟩
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 n.val = g n.val
      rw [Subtype.val_injective.extend_apply]
      change inner ℂ (completedBasisState n)
        ((ρN.op * B) (completedBasisState n)) =
        inner ℂ (completedBasisState n.val)
          ((ρF.op * A) (completedBasisState n.val))
      rw [hop]
      simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
      change inner ℂ (completedBasisState n)
        (ρN.op (V (A (U (completedBasisState n))))) =
        inner ℂ (completedBasisState n.val)
          (U (ρN.op (V (A (completedBasisState n.val)))))
      have hU : U (completedBasisState n) = completedBasisState n.val := by
        change completedCoordinateEmbedding
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective (completedBasisState n) = completedBasisState n.val
        exact completedCoordinateEmbedding_basisState _ _ n
      rw [hU]
      simp only [inner_completedBasisState_left]
      change
        (ρN.op (V (A (completedBasisState n.val)))) n =
          (completedCoordinateEmbedding
            (Subtype.val : ParticleNumberSector Mode Config N → Config)
            Subtype.val_injective
            (ρN.op (V (A (completedBasisState n.val))))) n.val
      rw [completedCoordinateEmbedding_apply, Subtype.val_injective.extend_apply]
    · have hnot : ¬ ∃ n : ParticleNumberSector Mode Config N, n.val = c := by
        rintro ⟨n, hn⟩
        apply hc
        rw [← hn]
        exact n.property
      change Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0 c = g c
      rw [Function.extend_apply' _ _ _ hnot]
      change (0 : ℂ) =
        inner ℂ (completedBasisState c) ((ρF.op * A) (completedBasisState c))
      rw [hop]
      simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply]
      change (0 : ℂ) =
        inner ℂ (completedBasisState c)
          (U (ρN.op (V (A (completedBasisState c)))))
      rw [inner_completedBasisState_left]
      change (0 : ℂ) =
        (completedCoordinateEmbedding
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective
          (ρN.op (V (A (completedBasisState c))))) c
      rw [completedCoordinateEmbedding_apply, Function.extend_apply' _ _ _ hnot]
      simp
  have hExtended : HasSum
      (Function.extend
        (Subtype.val : ParticleNumberSector Mode Config N → Config) f 0)
      (ρN.expectation B) :=
    (hasSum_extend_zero Subtype.val_injective).2 hSector
  rw [hPoint] at hExtended
  change ρF.expectation A = ρN.expectation B
  exact hFull.unique hExtended

end

end Common
end SecondQuantization
