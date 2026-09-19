import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Dyson coefficients as `Finset`-indexed vertex moments

This file is the seam between normalized fermionic Dyson partition coefficients, indexed by
perturbation order `ℕ`, and labelled finite-set vertex moments used by diagrammatic consumers.
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

end Fermionic
end SecondQuantization
