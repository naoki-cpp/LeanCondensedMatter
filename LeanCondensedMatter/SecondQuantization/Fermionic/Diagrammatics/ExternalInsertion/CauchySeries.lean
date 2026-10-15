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
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
  classical
  have slice : ∀ {n m k : ℕ}, m + k = n →
      (∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
        ∑ p : {ext : ExternalInsertionDiagram
            (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) E n T //
            HasNoVacuumComponent ext.vertexGraph} ×
            QuarticDiagram (QuarticVertexLabel Mode) n
              ((Finset.univ : Finset (Fin n)) \ T),
          if p.1.1.externalLabel = externalLabel then
            ExternalInsertionWickDiagram.dysonAmplitude
              (((ExternalInsertionDiagram.externalSupportFiberEquiv
                (Finset.subset_univ T)).symm p).1 :
                  ExternalInsertionWickDiagram Mode E n)
              ε β g externalTime
          else 0) =
        vacuumFreeExternalInsertionDysonCoefficient
          ε β g externalLabel externalTime m *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
    intro n m k hmk
    subst n
    exact externalInsertionFixedCardinalityFiberSum_eq_cauchyFactor
      ε β hβ g externalLabel externalTime m k
  rw [externalInsertionDysonCoefficient_eq_sum_powersetCard_externalSupportFiber]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by
    simpa [Nat.lt_succ_iff] using hm
  exact slice (Nat.add_sub_of_le hmn)

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
          (dysonPartitionSeries ε β (quarticInteraction g)) := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [externalInsertionDysonSeries, vacuumFreeExternalInsertionDysonSeries,
    PowerSeries.coeff_mk,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  exact externalInsertionDysonCoefficient_eq_sum_vacuumFree_mul_normalizedDysonPartitionCoeff
    ε β hβ g externalLabel externalTime n

/-- Vacuum normalization of the diagrammatic arbitrary-external Dyson series
removes exactly the pure-vacuum connected components. Distinct components
meeting the external sector need not be connected to one another. -/
theorem vacuumNormalizedExternalInsertionDysonSeries_eq_vacuumFreeExternalInsertionDysonSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    vacuumNormalizedExternalInsertionDysonSeries ε β g externalLabel externalTime =
      vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime := by
  exact (vacuumNormalizedExternalInsertionDysonSeries_eq_vacuumFree_iff_cauchy
    ε β g externalLabel externalTime).2
    (fun n => externalInsertionDysonCoefficient_eq_sum_vacuumFree_mul_normalizedDysonPartitionCoeff
      ε β hβ g externalLabel externalTime n)

end Fermionic
end SecondQuantization
