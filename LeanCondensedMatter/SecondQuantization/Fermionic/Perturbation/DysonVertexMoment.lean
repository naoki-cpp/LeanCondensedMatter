import LeanCondensedMatter.Analysis.PowerSeries.Moment
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator

set_option linter.style.header false

/-!
# Fermionic Gibbs realization of generic normalized Dyson moments

Factorial-normalized Dyson moments use the generic power-series moment coefficients rather than
a separate Dyson-specific definition. This file identifies that moment with the fermionic free
Gibbs density-state expectation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- The generic normalized Dyson series moment is the factorial times the fermionic free Gibbs
density-state expectation of the bare Dyson coefficient. -/
theorem powerSeriesMomentCoeff_dysonTraceSeries_eq_freeGibbsDensityOperator_expectation
    {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) :
    Combinatorics.powerSeriesMomentCoeff
        (PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β V)) S.card =
      (S.card.factorial : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperatorAlgEquiv
            (Common.dysonCoeff (fermionEnergy ε) V S.card β)) := by
  rw [Combinatorics.powerSeriesMomentCoeff,
    Common.coeff_normalizeByConstantCoeff_dysonTraceSeries_eq_finiteGibbsExpectation,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]

end Fermionic
end SecondQuantization
