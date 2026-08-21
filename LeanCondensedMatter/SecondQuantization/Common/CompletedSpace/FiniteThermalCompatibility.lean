import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

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
theorem completedFiniteHilbertEquiv_intertwines_finitePurePointGibbsDensity
    (energy : Config → ℝ) (β : ℝ) :
    (completedFiniteHilbertContinuousEquiv
      (Config := Config)).toContinuousLinearMap.comp
        (finitePurePointGibbsDensityOperator
          (completedHilbertBasis (Config := Config)) energy β).op =
      (finitePurePointGibbsDensityOperator
        (finiteHilbertBasis (Config := Config)) energy β).op.comp
        (completedFiniteHilbertContinuousEquiv
          (Config := Config)).toContinuousLinearMap := by
  apply continuousLinearMap_ext_completedBasis
  intro c
  simp only [ContinuousLinearMap.comp_apply]
  rw [← completedHilbertBasis_apply (Config := Config) c,
    finitePurePointGibbsDensityOperator_apply_basis, map_smul,
    completedHilbertBasis_apply]
  change (purePointGibbsProbability energy β c : ℂ) •
      completedFiniteHilbertEquiv (Config := Config) (completedBasisState c) =
    (finitePurePointGibbsDensityOperator
      (finiteHilbertBasis (Config := Config)) energy β).op
      (completedFiniteHilbertEquiv (Config := Config) (completedBasisState c))
  rw [completedFiniteHilbertEquiv_basisState,
    ← finiteHilbertBasis_apply (Config := Config) c,
    finitePurePointGibbsDensityOperator_apply_basis,
    finiteHilbertBasis_apply]

end
end Common
end SecondQuantization
