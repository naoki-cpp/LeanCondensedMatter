import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

The normalized finite-configuration vertex moments live in Common. This file identifies that
generic moment with the fermionic free Gibbs density-state expectation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
private theorem normalizedDysonPartitionCoeff_eq_freeGibbsDensityOperator_expectation
    (ε : Mode → ℝ) (β : ℝ) (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    normalizedDysonPartitionCoeff ε β V n =
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (Common.dysonCoeff (fermionEnergy ε) V n β)) := by
  have hZ : Common.traceFock (Common.diagonalEvolution (fermionEnergy ε) (-β)) =
      freePartitionFunction ε β := by
    simpa [Common.weightSum, freePartitionFunction, freeBoltzmannWeight] using
      (Common.traceFock_diagonalEvolution_eq_weightSum (fermionEnergy ε) β)
  rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_eq_trace_div,
    normalizedDysonPartitionCoeff, hZ]
  congr 1

/-- The Common normalized finite-configuration coefficient specializes to the fermionic
partition-function normalization. -/
private theorem normalizedDysonTraceCoeff_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (n : ℕ) :
    Common.normalizedDysonTraceCoeff (fermionEnergy ε) β V n =
      normalizedDysonPartitionCoeff ε β V n := by
  change Common.dysonTraceCoeff (fermionEnergy ε) β V n /
      PowerSeries.constantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β V) =
    dysonPartitionCoeff ε β V n / freePartitionFunction ε β
  rw [← constantCoeff_dysonPartitionSeries ε β V]
  rfl

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
    normalizedDysonTraceCoeff_eq_normalizedDysonPartitionCoeff,
    normalizedDysonPartitionCoeff_eq_freeGibbsDensityOperator_expectation]

end Fermionic
end SecondQuantization
