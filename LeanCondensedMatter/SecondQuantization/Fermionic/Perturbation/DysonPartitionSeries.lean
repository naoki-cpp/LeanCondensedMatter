import LeanCondensedMatter.Analysis.PowerSeries.Normalization
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore

set_option linter.style.header false

/-!
# The fermionic Dyson partition-function series

The fermionic Dyson partition coefficients and series are the occupation-Fock specialization of the
statistics-independent Dyson trace expansion in
`SecondQuantization.Common.Perturbation.DysonTraceSeries`.

The constant coefficient is identified with the free fermionic partition function. Dividing by that
nonzero constant term gives the normalized coefficients, and the normalized series supplies the
formal logarithm used for connected perturbative expansions.
-/

namespace SecondQuantization
namespace Fermionic

open PowerSeries

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The fermionic finite Dyson partition-function coefficient. -/
noncomputable def dysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) : ℂ :=
  Common.dysonTraceCoeff (fermionEnergy ε) β V n

omit [LinearOrder Mode] in
/-- The fermionic coefficient is the specialization of the Common Dyson trace coefficient. -/
theorem dysonPartitionCoeff_eq_dysonTraceCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    dysonPartitionCoeff ε β V n = Common.dysonTraceCoeff (fermionEnergy ε) β V n := rfl

/-- The fermionic specialization of `Common.dysonTraceSeries`. -/
noncomputable def dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) : PowerSeries ℂ :=
  Common.dysonTraceSeries (fermionEnergy ε) β V

omit [LinearOrder Mode] in
/-- Coefficients are the fermionic Dyson partition coefficients. -/
theorem coeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    PowerSeries.coeff n (dysonPartitionSeries ε β V) = dysonPartitionCoeff ε β V n := by
  rw [dysonPartitionCoeff_eq_dysonTraceCoeff]
  exact Common.coeff_dysonTraceSeries (fermionEnergy ε) β V n

omit [LinearOrder Mode] in
/-- The constant coefficient is the fermionic free partition function. -/
theorem constantCoeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    PowerSeries.constantCoeff (dysonPartitionSeries ε β V) = freePartitionFunction ε β := by
  simpa [dysonPartitionSeries, Common.weightSum, freePartitionFunction, freeBoltzmannWeight] using
    (Common.constantCoeff_dysonTraceSeries (fermionEnergy ε) β V)

omit [LinearOrder Mode] in
/-- The Dyson partition series has nonzero constant coefficient, so canonical normalization is
available. -/
theorem constantCoeff_dysonPartitionSeries_ne_zero (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    PowerSeries.constantCoeff (dysonPartitionSeries ε β V) ≠ 0 := by
  rw [constantCoeff_dysonPartitionSeries]
  exact freePartitionFunction_ne_zero ε β

omit [LinearOrder Mode] in
@[simp]
theorem dysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    dysonPartitionCoeff ε β V 0 = freePartitionFunction ε β := by
  rw [← coeff_dysonPartitionSeries, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_dysonPartitionSeries]

/-- The normalized fermionic Dyson partition coefficient. -/
noncomputable def normalizedDysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) : ℂ :=
  dysonPartitionCoeff ε β V n / freePartitionFunction ε β

omit [LinearOrder Mode] in
/-- Coefficients of the normalized Dyson partition series are the normalized fermionic Dyson
partition coefficients. -/
theorem coeff_normalizeByConstantCoeff_dysonPartitionSeries_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) =
      normalizedDysonPartitionCoeff ε β V n := by
  rw [normalizedDysonPartitionCoeff, PowerSeries.coeff_normalizeByConstantCoeff,
    constantCoeff_dysonPartitionSeries, coeff_dysonPartitionSeries, div_eq_mul_inv]
  exact mul_comm _ _

omit [LinearOrder Mode] in
@[simp]
theorem normalizedDysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    normalizedDysonPartitionCoeff ε β V 0 = 1 := by
  rw [normalizedDysonPartitionCoeff, dysonPartitionCoeff_zero,
    div_self (freePartitionFunction_ne_zero ε β)]

/-- The normalized logarithm of the fermionic Dyson partition series. -/
noncomputable def dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) : PowerSeries ℂ :=
  PowerSeries.logOf
    (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))

end Fermionic
end SecondQuantization
