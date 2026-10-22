import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateIsometry
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.CoordinateProjection
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Fixed-particle-number canonical Gibbs states

The canonical ensemble at sharp particle number `N` is built on the Hilbert space
`ℓ²(ParticleNumberSector Mode Config N, ℂ)`. This construction depends only on the
statistics-independent occupation number and free occupation energy.

Normalization reuses `QuantumTheory.eigenbasisGibbsDensityOperator`. A sector need
not be nonempty, and even a nonempty sector can have infinitely many configurations:
both nonemptiness and Boltzmann summability are explicit prerequisites.

This is a sector state, not its zero extension to the full occupation Fock space.
No Gaussian/Wick or full-field KMS property is asserted.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Mode Config : Type*} [OccupationBasis Mode Config]

/-- The free canonical partition function over configurations with exactly `N` particles.
Finiteness of this sum is a separate hypothesis when constructing a state. -/
noncomputable def canonicalPartitionFunction
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) : ℝ :=
  eigenbasisPartitionFunction
    (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β

/-- The canonical Gibbs state on the completed fixed-number sector. -/
noncomputable def canonicalGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    DensityOperator (CompletedFock (ParticleNumberSector Mode Config N)) :=
  eigenbasisGibbsDensityOperator
    (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
    (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β hsum

/-- Summable canonical Boltzmann weights give a strictly positive partition function
whenever the fixed-number sector is nonempty. -/
theorem canonicalPartitionFunction_pos
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    0 < canonicalPartitionFunction (Config := Config) ε β N := by
  exact eigenbasisPartitionFunction_pos
    (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β hsum

/-- The canonical density acts by normalized Boltzmann probabilities in its own sector. -/
@[simp]
theorem canonicalGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β)
    (n : ParticleNumberSector Mode Config N) :
    (canonicalGibbsDensityOperator (Config := Config) ε β N hsum).op
        (completedBasisState n) =
      (eigenbasisGibbsProbability
        (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β n : ℂ) •
        completedBasisState n := by
  simpa [canonicalGibbsDensityOperator, completedHilbertBasis_apply] using
    (eigenbasisGibbsDensityOperator_apply_basis
      (completedHilbertBasis (Config := ParticleNumberSector Mode Config N))
      (fun m : ParticleNumberSector Mode Config N => occupationEnergy ε m.val) β hsum n)


/-- A uniform one-particle energy shift is constant on a fixed-number sector. -/
private theorem canonicalSectorEnergy_shift_eq (ε : Mode → ℝ) (N : ℕ) (C : ℝ) :
    (fun n : ParticleNumberSector Mode Config N =>
      occupationEnergy (fun i => ε i + C) n.val) =
    (fun n : ParticleNumberSector Mode Config N =>
      occupationEnergy ε n.val + C * (N : ℝ)) := by
  funext n
  rw [occupationEnergy_add_const, n.property]

/-- An energy-reference shift does not change convergence of the canonical
sector Boltzmann weights. -/
theorem canonicalGibbsSummable_shift (ε : Mode → ℝ) (β : ℝ) (N : ℕ) (C : ℝ)
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N =>
        occupationEnergy (fun i => ε i + C) n.val) β := by
  rw [canonicalSectorEnergy_shift_eq]
  exact eigenbasisGibbsSummable_add_const
    (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val)
    β (C * (N : ℝ)) hsum

/-- Shifting all single-particle energies by the same constant leaves the
normalized canonical Gibbs state on a fixed-number sector unchanged. -/
theorem canonicalGibbsDensityOperator_shift_invariant
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) (C : ℝ)
    [Nonempty (ParticleNumberSector Mode Config N)]
    (hsum : EigenbasisGibbsSummable
      (fun n : ParticleNumberSector Mode Config N => occupationEnergy ε n.val) β) :
    canonicalGibbsDensityOperator (Config := Config) (fun i => ε i + C) β N
        (canonicalGibbsSummable_shift ε β N C hsum) =
      canonicalGibbsDensityOperator (Config := Config) ε β N hsum := by
  classical
  apply DensityOperator.ext
  apply continuousLinearMap_ext_completedBasis
  intro n
  rw [canonicalGibbsDensityOperator_apply_basis,
    canonicalGibbsDensityOperator_apply_basis]
  rw [canonicalSectorEnergy_shift_eq, eigenbasisGibbsProbability_add_const]


/-- Pullback after zero-extension from the fixed-number sector is the identity.
This works for arbitrary mode types and does not require Gibbs summability. -/
theorem canonicalSectorPullback_comp_embedding (N : ℕ) :
    (completedCoordinatePullback
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      Subtype.val_injective).comp
      (completedCoordinateEmbedding
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (CompletedFock (ParticleNumberSector Mode Config N)) := by
  classical
  apply ContinuousLinearMap.ext
  intro ψ
  ext n
  rw [ContinuousLinearMap.comp_apply, completedCoordinatePullback_apply]
  change Function.extend
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      (fun d => ψ d) 0 n.val = ψ n
  simp only [Subtype.val_injective.extend_apply]

/-- The fixed-particle-number coordinate projection is precisely zero-extension
from the sector composed with coordinate pullback onto that sector.
This is the operator-level bridge needed to extend canonical states to full Fock space. -/
theorem completedParticleNumberProjection_eq_embedding_comp_pullback (N : ℕ) :
    completedCoordinateProjection (fun c : Config => particleNumber (Mode := Mode) c = N) =
      (completedCoordinateEmbedding
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective).toContinuousLinearMap.comp
        (completedCoordinatePullback
          (Subtype.val : ParticleNumberSector Mode Config N → Config)
          Subtype.val_injective) := by
  classical
  apply ContinuousLinearMap.ext
  intro ψ
  ext c
  rw [completedCoordinateProjection_apply, ContinuousLinearMap.comp_apply]
  change (if particleNumber (Mode := Mode) c = N then ψ c else 0) =
    Function.extend
      (Subtype.val : ParticleNumberSector Mode Config N → Config)
      (fun n => completedCoordinatePullback
        (Subtype.val : ParticleNumberSector Mode Config N → Config)
        Subtype.val_injective ψ n) 0 c
  by_cases hc : particleNumber (Mode := Mode) c = N
  · let d : ParticleNumberSector Mode Config N := ⟨c, hc⟩
    rw [show c = (d : Config) from rfl,
      Subtype.val_injective.extend_apply, completedCoordinatePullback_apply]
    simp [hc, d]
  · have hnot : ¬ ∃ d : ParticleNumberSector Mode Config N, (d : Config) = c := by
      rintro ⟨d, hd⟩
      apply hc
      rw [← hd]
      exact d.property
    rw [Function.extend_apply' _ _ _ hnot]
    simp [hc]

end

end Common
end SecondQuantization
