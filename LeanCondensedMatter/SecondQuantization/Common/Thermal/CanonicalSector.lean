import LeanCondensedMatter.SecondQuantization.Common.Algebra.OccupationBasis
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.Basic
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

end

end Common
end SecondQuantization
