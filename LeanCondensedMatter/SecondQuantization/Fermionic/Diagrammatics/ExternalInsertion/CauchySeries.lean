import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumFiberCauchySum

set_option linter.style.header false

/-!
# Vacuum-free arbitrary-external Dyson series

The fixed-cardinality support-fiber factorization gives a Cauchy convolution at
each total interaction order. The corresponding formal Dyson series therefore
factors into a vacuum-free external-insertion series and the normalized vacuum
partition series. Cancelling the vacuum factor removes only purely vacuum
components, without identifying the higher-point result with a cumulant or a
fully connected external-insertion correlation function.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The arbitrary-external Dyson coefficient is the Cauchy convolution of
vacuum-free external-insertion coefficients and normalized vacuum coefficients. -/
theorem externalInsertionDysonCoefficient_eq_sum_vacuumFree_mul_normalizedDysonPartitionCoeff
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionDysonCoefficient ε β g externalLabel externalTime n =
      ∑ m ∈ Finset.range (n + 1),
        vacuumFreeExternalInsertionDysonCoefficient
          ε β g externalLabel externalTime m *
          PowerSeries.coeff (n - m) (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) := by
  classical
  rw [externalInsertionDysonCoefficient_eq_sum_powersetCard_externalSupportFiber]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by
    simpa [Nat.lt_succ_iff] using hm
  simpa only [Nat.add_sub_of_le hmn] using
    (externalInsertionFixedCardinalityFiberSum_eq_cauchyFactor
      ε β hβ g externalLabel externalTime m (n - m))

/-- The full arbitrary-external Dyson series is the product of its vacuum-free
part and the normalized vacuum partition series. -/
theorem externalInsertionDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionDysonSeries ε β g externalLabel externalTime =
      vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [externalInsertionDysonSeries, vacuumFreeExternalInsertionDysonSeries,
    PowerSeries.coeff_mk]
  exact externalInsertionDysonCoefficient_eq_sum_vacuumFree_mul_normalizedDysonPartitionCoeff
    ε β hβ g externalLabel externalTime n

/-- Partition-function normalization of the diagrammatic arbitrary-external Dyson series
removes exactly the pure-vacuum connected components. Distinct components
meeting the external sector need not be connected to one another. -/
theorem partitionFunctionNormalizedExternalInsertionDysonSeries_eq_vacuumFreeExternalInsertionDysonSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    partitionFunctionNormalizedExternalInsertionDysonSeries ε β g externalLabel externalTime =
      vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime := by
  rw [partitionFunctionNormalizedExternalInsertionDysonSeries]
  apply PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
  · rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (Common.constantCoeff_dysonTraceSeries_ne_zero (fermionEnergy ε) β (quarticInteraction g))]
    exact one_ne_zero
  · exact externalInsertionDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
      ε β hβ g externalLabel externalTime

end Fermionic
end SecondQuantization
