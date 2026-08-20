import LeanCondensedMatter.Analysis.PowerSeries.LowOrderLog
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.LinkedCluster.Theorem

set_option linter.style.header false

/-!
# Low-order fermionic formal linked-cluster identities

The first three coefficients make the moment-cumulant subtraction pattern explicit and specialize
the general fermionic Dyson Linked Cluster Theorem to orders one, two, and three.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- At first order, the factorial-normalized logarithmic coefficient is the first normalized Dyson
coefficient. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_one
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((1 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 1
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 := by
  rw [dysonFormalLogPartitionFunction]
  simpa only [
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff] using
    (Combinatorics.factorial_mul_coeff_logOf_one_eq
      (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
        ε β (quarticInteraction g)))

/-- At second order, the logarithm subtracts the product of two first-order contributions. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((2 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 2
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 -
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 2 := by
  rw [dysonFormalLogPartitionFunction]
  simpa only [
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff] using
    (Combinatorics.factorial_mul_coeff_logOf_two_eq
      (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
        ε β (quarticInteraction g)))

/-- At third order, the logarithm removes the one-plus-two and three-singleton disconnected terms. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_three
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((3 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 3
          (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) =
      6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 3 -
        6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 +
        2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 3 := by
  rw [dysonFormalLogPartitionFunction]
  simpa only [
    coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff] using
    (Combinatorics.factorial_mul_coeff_logOf_three_eq
      (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
        ε β (quarticInteraction g)))

/-- First-order formal linked-cluster regression corollary. -/
theorem dysonFormalLinkedCluster_order_one
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 =
      ∑ d : ConnectedQuarticWickDiagram Mode 1 Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  calc
    normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 =
        ((1 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 1
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      (factorial_mul_coeff_dysonFormalLogPartitionFunction_order_one ε β g).symm
    _ = ∑ d : ConnectedQuarticWickDiagram Mode 1 Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
        ε β g 1 (by norm_num)

/-- Second-order formal linked-cluster regression corollary, displaying cancellation of the
product of two disconnected one-vertex contributions. -/
theorem dysonFormalLinkedCluster_order_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 -
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 2 =
      ∑ d : ConnectedQuarticWickDiagram Mode 2 Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  calc
    2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 -
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 2 =
        ((2 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 2
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      (factorial_mul_coeff_dysonFormalLogPartitionFunction_order_two ε β g).symm
    _ = ∑ d : ConnectedQuarticWickDiagram Mode 2 Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
        ε β g 2 (by norm_num)

/-- Third-order formal linked-cluster regression corollary, displaying cancellation of all
one-plus-two and three-singleton disconnected decompositions. -/
theorem dysonFormalLinkedCluster_order_three
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 3 -
        6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 +
        2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 3 =
      ∑ d : ConnectedQuarticWickDiagram Mode 3 Finset.univ,
        quarticWickDiagramAmplitude ε β g d.1 := by
  calc
    6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 3 -
        6 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) 2 +
        2 * normalizedDysonPartitionCoeff ε β (quarticInteraction g) 1 ^ 3 =
        ((3 : ℕ).factorial : ℂ) *
          PowerSeries.coeff 3
            (dysonFormalLogPartitionFunction ε β (quarticInteraction g)) :=
      (factorial_mul_coeff_dysonFormalLogPartitionFunction_order_three ε β g).symm
    _ = ∑ d : ConnectedQuarticWickDiagram Mode 3 Finset.univ,
          quarticWickDiagramAmplitude ε β g d.1 :=
      factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
        ε β g 3 (by norm_num)

end Fermionic
end SecondQuantization
