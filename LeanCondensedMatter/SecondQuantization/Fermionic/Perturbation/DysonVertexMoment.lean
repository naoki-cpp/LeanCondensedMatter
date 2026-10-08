import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

set_option linter.style.header false

/-!
# Fermionic realization of Common Dyson vertex moments

The normalized finite-configuration vertex moments live in Common. This file identifies that
generic moment with the fermionic free Gibbs density-state expectation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The Common finite-configuration Dyson moment is the factorial times the fermionic free Gibbs
density-state expectation of the bare Dyson coefficient. -/
theorem dysonTraceVertexMoment_eq_freeGibbsDensityOperator_expectation
    {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) :
    Common.dysonTraceVertexMoment (fermionEnergy ε) β V S =
      (S.card.factorial : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperatorAlgEquiv
            (Common.dysonCoeff (fermionEnergy ε) V S.card β)) := by
  rw [Common.dysonTraceVertexMoment,
    Common.normalizedDysonTraceCoeff_eq_finiteGibbsExpectation,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

end Fermionic
end SecondQuantization
