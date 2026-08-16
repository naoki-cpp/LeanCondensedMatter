import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.CauchyCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ConnectedSeries

set_option linter.style.header false

/-!
# Power-series form of the two-point linked-cluster theorem

The coefficientwise identity from `CauchyCoefficient` is already the Cauchy product of the connected
two-point coefficients with the normalized Dyson partition coefficients.  This file identifies that
second factor with `normalizeByConstantCoeff (dysonPartitionSeries ...)`, lifts the coefficientwise
identity to an equality of formal power series, and cancels the vacuum series from the existing
vacuum-normalized two-point series.

No diagrammatic decomposition is introduced here: this is only the formal power-series algebra after
the canonical external-slot fiber proof.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **Finite-mode fermionic two-point linked-cluster theorem.** For the imaginary-time Dyson series
built from free Gibbs expectations and a quartic interaction, with the repository's canonical
time-order/equal-time convention, vacuum normalization leaves exactly the sum of externally
connected two-point diagrams. -/
theorem vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    vacuumNormalizedTwoPointDysonSeries ε β g i j τ τ' =
      connectedTwoPointDysonSeries ε β g i j τ τ' := by
  let Z := PowerSeries.normalizeByConstantCoeff
    (dysonPartitionSeries ε β (quarticInteraction g))
  have hZ : Z ≠ 0 := by
    intro hz
    have hcoeff := congrArg PowerSeries.constantCoeff hz
    simpa [Z, constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries] using hcoeff
  apply mul_right_cancel₀ hZ
  rw [vacuumNormalizedTwoPointDysonSeries_mul_normalizeByConstantCoeff]
  dsimp [Z]
  ext n
  rw [coeff_twoPointDysonSeries, PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  simp only [coeff_connectedTwoPointDysonSeries,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  exact twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    ε β hβ g i j τ τ' n

end Fermionic
end SecondQuantization
