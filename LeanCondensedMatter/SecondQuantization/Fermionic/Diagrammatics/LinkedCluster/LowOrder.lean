import LeanCondensedMatter.Analysis.PowerSeries.LowOrderLog
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries

set_option linter.style.header false

/-!
# Low-order fermionic formal logarithm identities

The first three coefficients of the normalized fermionic Dyson-series logarithm display the
moment-cumulant subtraction pattern explicitly. They are low-order corollaries of the general
formal linked-cluster construction; connected-diagram statements are supplied by the general
linked-cluster theorem rather than separate low-order definitions.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- At first order, the factorial-normalized logarithmic coefficient is the first normalized Dyson
coefficient. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_one
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((1 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 1
          (PowerSeries.logOf (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))) =
      PowerSeries.coeff 1 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) := by
  simpa only [] using
    (Combinatorics.factorial_mul_coeff_logOf_one_eq
      (PowerSeries.constantCoeff_normalizeByConstantCoeff
        (Common.constantCoeff_dysonTraceSeries_ne_zero (fermionEnergy ε) β (quarticInteraction g))))

/-- At second order, the logarithm subtracts the product of two first-order contributions. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_two
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((2 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 2
          (PowerSeries.logOf (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))) =
      2 * PowerSeries.coeff 2 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) -
        PowerSeries.coeff 1 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) ^ 2 := by
  simpa only [] using
    (Combinatorics.factorial_mul_coeff_logOf_two_eq
      (PowerSeries.constantCoeff_normalizeByConstantCoeff
        (Common.constantCoeff_dysonTraceSeries_ne_zero (fermionEnergy ε) β (quarticInteraction g))))

/-- At third order, the logarithm removes the one-plus-two and three-singleton disconnected terms. -/
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_order_three
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ((3 : ℕ).factorial : ℂ) *
        PowerSeries.coeff 3
          (PowerSeries.logOf (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))) =
      6 * PowerSeries.coeff 3 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) -
        6 * PowerSeries.coeff 1 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) *
          PowerSeries.coeff 2 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) +
        2 * PowerSeries.coeff 1 (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) ^ 3 := by
  simpa only [] using
    (Combinatorics.factorial_mul_coeff_logOf_three_eq
      (PowerSeries.constantCoeff_normalizeByConstantCoeff
        (Common.constantCoeff_dysonTraceSeries_ne_zero (fermionEnergy ε) β (quarticInteraction g))))

end Fermionic
end SecondQuantization
