import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs

set_option linter.style.header false

/-!
# Finite-mode compatibility of the completed free Gibbs state

For finitely many fermionic modes, the completed occupation space and the existing finite Hilbert
Fock realization are canonically isometric.  In this setting every occupation-indexed Boltzmann
family is automatically summable, and the completed and finite partition functions, normalized
probabilities, and diagonal Gibbs density operators describe the same state under that isometry.
-/

namespace SecondQuantization
namespace Fermionic

noncomputable section

variable {Mode : Type*}

/-- The normalized completed Gibbs probability is the normalized finite Boltzmann weight. -/
theorem completedFreeGibbsProbability_eq_finite
    (ε : Mode → ℝ) (β : ℝ) (n : Occupation Mode) :
    completedFreeGibbsProbability ε β n =
      (Common.finitePartitionFunction (fermionEnergy ε) β)⁻¹ *
        Common.finiteBoltzmannWeight (fermionEnergy ε) β n := by
  rfl

variable [Fintype Mode]

/-- Under the canonical finite-mode isometry, the completed free Gibbs density operator is exactly
the existing finite Gibbs density operator. -/
theorem completedFiniteHilbertEquiv_intertwines_freeGibbsDensity
    (ε : Mode → ℝ) (β : ℝ) (hsum : CompletedFreeGibbsSummable ε β) :
    (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap.comp
        (completedFreeGibbsDensityOperator ε β hsum).op =
      (Common.finiteGibbsDensityOperator (fermionEnergy ε) β).op.comp
        (completedFiniteHilbertContinuousEquiv (Mode := Mode)).toContinuousLinearMap := by
  apply continuousLinearMap_ext_completedBasis_to_finite
  intro n
  simp only [ContinuousLinearMap.comp_apply]
  rw [completedFreeGibbsDensityOperator_apply_basis, map_smul]
  change (completedFreeGibbsProbability ε β n : ℂ) •
      completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n) =
    (Common.finiteGibbsDensityOperator (fermionEnergy ε) β).op
      (completedFiniteHilbertEquiv (Mode := Mode) (completedBasisState n))
  rw [completedFiniteHilbertEquiv_basisState,
    Common.finiteGibbsDensityOperator_apply_basis,
    completedFreeGibbsProbability_eq_finite]

end
end Fermionic
end SecondQuantization
