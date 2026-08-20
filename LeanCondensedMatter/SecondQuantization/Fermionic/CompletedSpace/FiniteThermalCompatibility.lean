import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs
import LeanCondensedMatter.SecondQuantization.Common.Thermal.PurePointCompatibility

set_option linter.style.header false

/-!
# Finite-mode compatibility of the completed free Gibbs state

For finitely many fermionic modes, the completed occupation space and the existing finite Hilbert
Fock realization are canonically isometric.  The completed free Gibbs state is the generic
pure-point Gibbs state on the occupation basis, while the finite Hilbert Gibbs state is its finite
specialization.  The same pure-point probabilities therefore describe both states under the
canonical isometry.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Under the canonical finite-mode isometry, the generic pure-point free Gibbs density operator on
completed Fock space is exactly the existing finite Gibbs density operator. -/
theorem completedFiniteHilbertEquiv_intertwines_freeGibbsDensity
    (ε : Mode → ℝ) (β : ℝ) (hsum : PurePointGibbsSummable (fermionEnergy ε) β) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp
        (purePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β hsum).op =
      (Common.finiteGibbsDensityOperator (fermionEnergy ε) β).op.comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  apply continuousLinearMap_ext_completedBasis_to_finite
  intro n
  simp only [ContinuousLinearMap.comp_apply]
  rw [completedFreeGibbsDensityOperator_apply_basis, map_smul]
  change (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) •
      completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n) =
    (Common.finiteGibbsDensityOperator (fermionEnergy ε) β).op
      (completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n))
  rw [completedFiniteHilbertEquiv_basisState,
    Common.finiteGibbsDensityOperator_apply_basis_eq_purePointProbability]

end
end Fermionic
end SecondQuantization
