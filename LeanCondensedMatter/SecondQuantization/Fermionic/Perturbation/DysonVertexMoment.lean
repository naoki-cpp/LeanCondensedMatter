import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.GeneratingFunctional
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.GibbsExpectation.Core

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

This file is the seam between normalized fermionic Dyson partition coefficients, indexed by
perturbation order `ℕ`, and labelled finite-set vertex moments. It also packages those moments as the
statistics-independent source generating functional used by linked-cluster consumers.
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

/-- The factorial-normalized Dyson vertex moment on a finite vertex set. -/
noncomputable def dysonVertexMoment {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) : ℂ :=
  (S.card.factorial : ℂ) * normalizedDysonPartitionCoeff ε β V S.card

omit [LinearOrder Mode] in
/-- The Dyson vertex moment is the factorial times the canonical free Gibbs density-state
expectation of the bare Dyson coefficient at the corresponding order. -/
theorem dysonVertexMoment_eq_freeGibbsDensityOperator_expectation
    {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) :
    dysonVertexMoment ε β V S =
      (S.card.factorial : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperatorAlgEquiv
            (Common.dysonCoeff (fermionEnergy ε) V S.card β)) := by
  rw [dysonVertexMoment,
    normalizedDysonPartitionCoeff_eq_freeGibbsDensityOperator_expectation]

/-- The normalized Dyson vertex moments as a source generating functional. -/
noncomputable def dysonVertexGeneratingFunctional {α : Type*} [DecidableEq α]
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.GeneratingFunctional α ℂ :=
  Common.powerSeriesGeneratingFunctional
    (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))
    (PowerSeries.constantCoeff_normalizeByConstantCoeff
      (constantCoeff_dysonPartitionSeries_ne_zero ε β V))

omit [LinearOrder Mode] in
/-- The source-functional moments are exactly the labelled Dyson vertex moments. -/
theorem dysonVertexGeneratingFunctional_moment {α : Type*} [DecidableEq α]
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (S : Finset α) :
    (dysonVertexGeneratingFunctional ε β V).moment S = dysonVertexMoment ε β V S := by
  change Combinatorics.powerSeriesMomentCoeff
      (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) S.card =
    dysonVertexMoment ε β V S
  rw [Combinatorics.powerSeriesMomentCoeff, dysonVertexMoment,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]

end Fermionic
end SecondQuantization