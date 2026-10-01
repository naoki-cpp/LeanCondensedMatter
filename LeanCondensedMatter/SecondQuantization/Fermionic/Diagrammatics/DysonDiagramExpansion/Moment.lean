import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Reindexing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Wick.Connected

set_option linter.style.header false

/-!
# Fermionic Dyson diagram moments

Bundles the coefficientwise Dyson-to-Wick expansion as an equality of normalized finite-set
moments. This is the semantic boundary consumed by the fermionic linked-cluster theorem.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Factorial-normalized coefficients of the normalized fermionic Dyson partition series are
exactly the bundled Dyson vertex moments. -/
theorem powerSeriesMomentSetFunction_normalizedDysonPartitionSeries_eq_dysonVertexMomentSetFunction
    {α : Type*} (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (hZ :
      PowerSeries.constantCoeff
          (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) = 1) :
    Combinatorics.powerSeriesMomentSetFunction (α := α)
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) hZ =
      dysonVertexMomentSetFunction ε β V := by
  rw [Combinatorics.powerSeriesMomentSetFunction_eq_iff]
  intro S
  simp only [Combinatorics.powerSeriesMomentCoeff, dysonVertexMomentSetFunction_apply,
    dysonVertexMoment,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]

/-- The factorial-normalized fermionic Dyson vertex moment is exactly the normalized total
quartic Wick-diagram moment. -/
theorem dysonVertexMomentSetFunction_eq_quarticWickDiagramMoment
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {N : ℕ} :
    dysonVertexMomentSetFunction (α := Fin N) ε β (quarticInteraction g) =
      quarticWickDiagramMoment (N := N) ε β g := by
  ext S
  change
    dysonVertexMoment ε β (quarticInteraction g) S =
      ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
  exact dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude ε β g S

end Fermionic
end SecondQuantization
