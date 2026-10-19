import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Finite thermal compatibility of completed Fock space

For a finite configuration type, the canonical isometry from the completed `ℓ²` realization to the
finite Euclidean Hilbert realization intertwines the corresponding finite pure-point Gibbs density
operators. This depends only on the configuration basis and its energy function, not on particle
statistics.
-/

namespace SecondQuantization
namespace Common

open QuantumTheory

noncomputable section

variable {Config : Type*} [Fintype Config] [Nonempty Config]

/-- The canonical finite-configuration isometry intertwines the pure-point Gibbs density operator
on completed Fock space with the same density operator on the finite Hilbert realization. -/
theorem completedFiniteHilbertEquiv_intertwines_eigenbasisGibbsDensity
    (energy : Config → ℝ) (β : ℝ) :
    (completedFiniteHilbertEquiv
      (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (eigenbasisGibbsDensityOperator
          (completedHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).op =
      (eigenbasisGibbsDensityOperator
        (finiteHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).op.comp
        (completedFiniteHilbertEquiv
          (Config := Config)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply continuousLinearMap_ext_completedBasis
  intro c
  simp only [ContinuousLinearMap.comp_apply]
  rw [← completedHilbertBasis_apply (Config := Config) c,
    eigenbasisGibbsDensityOperator_apply_basis, map_smul,
    completedHilbertBasis_apply]
  change (eigenbasisGibbsProbability energy β c : ℂ) •
      completedFiniteHilbertEquiv (Config := Config) (completedBasisState c) =
    (eigenbasisGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β
        (eigenbasisGibbsSummable_of_finite energy β)).op
      (completedFiniteHilbertEquiv (Config := Config) (completedBasisState c))
  rw [completedFiniteHilbertEquiv_basisState,
    ← finiteHilbertBasis_apply (Config := Config) c,
    eigenbasisGibbsDensityOperator_apply_basis,
    finiteHilbertBasis_apply]

end
end Common
end SecondQuantization
