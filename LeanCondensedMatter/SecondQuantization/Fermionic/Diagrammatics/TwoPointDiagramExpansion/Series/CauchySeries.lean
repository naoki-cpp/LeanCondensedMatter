import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.FiberCauchySum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.DysonSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
# Cauchy convolution and power-series linked-cluster theorem

The canonical external-slot fiber decomposition first identifies each order-`n` two-point Dyson
coefficient with the Cauchy convolution of externally connected coefficients and normalized vacuum
coefficients.  The same module then lifts that coefficientwise identity to formal power series and
cancels the normalized vacuum series.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **Coefficientwise linked-cluster Cauchy identity.**

At order `n`, the complete operator-defined two-point Dyson coefficient is the Cauchy convolution of
the connected two-point coefficients with the normalized vacuum partition coefficients. -/
theorem twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointDysonCoefficient (n := n) ε β g i j τ τ' =
      ∑ m ∈ Finset.range (n + 1),
        connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
  rw [← twoPointDiagramCoefficient_eq_twoPointDysonCoefficient]
  classical
  have slice : ∀ {n m k : ℕ}, m + k = n →
      (∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
        ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
                ext.1.IsExternallyConnected} ×
              QuarticWickDiagram Mode n
                ((Finset.univ : Finset (Fin n)) \ T),
          ((fixedExternalFiberEquiv T).symm p).1.dysonAmplitude ε β g τ τ') =
        connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
    intro n m k hmk
    subst n
    rw [Finset.sum_subtype
      (p := fun T : Finset (Fin (m + k)) => T.card = m)
      (Finset.powersetCard m (Finset.univ : Finset (Fin (m + k))))
      (fun T => by simp)
      (fun T =>
        ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) T i j //
                ext.1.IsExternallyConnected} ×
              QuarticWickDiagram Mode (m + k)
                ((Finset.univ : Finset (Fin (m + k))) \ T),
          ((fixedExternalFiberEquiv T).symm p).1.dysonAmplitude ε β g τ τ')]
    exact fixedExternalFiberSum_eq_cauchyFactor
      ε β hβ g i j τ τ' m k
  rw [twoPointDiagramCoefficient_eq_sum_dysonAmplitude]
  rw [sum_eq_sum_powerset_fixedExternalFiber
    (Mode := Mode) (i := i) (j := j)
    (F := fun d => d.dysonAmplitude ε β g τ τ')]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by
    simpa [Nat.lt_succ_iff] using hm
  exact slice (Nat.add_sub_of_le hmn)

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
  dsimp [Z] at hZ ⊢
  rw [vacuumNormalizedTwoPointDysonSeries, mul_assoc,
    PowerSeries.inv_mul_cancel _ (by
      rw [constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries]
      exact one_ne_zero),
    mul_one]
  ext n
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [twoPointDysonSeries, connectedTwoPointDysonSeries, PowerSeries.coeff_mk,
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff]
  exact twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    ε β hβ g i j τ τ' n

end Fermionic
end SecondQuantization
