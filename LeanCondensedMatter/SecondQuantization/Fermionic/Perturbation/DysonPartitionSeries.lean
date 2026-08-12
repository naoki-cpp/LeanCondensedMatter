import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.Analysis.PowerSeries.Normalization

set_option linter.style.header false

/-!
# The fermionic Dyson partition-function series

The statistics-independent implementation is supplied by
`SecondQuantization.Common.Perturbation.DysonTraceSeries`. The fermionic coefficient name is
retained because it denotes a physical partition-function coefficient, not a compatibility alias.
Power-series normalization and logarithms use their canonical `PowerSeries` names directly.
-/

namespace SecondQuantization
namespace Fermionic

open PowerSeries

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The fermionic finite Dyson partition-function coefficient. -/
noncomputable def dysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ) : ℂ :=
  Common.traceFock
    ((imaginaryTimeEvolveFree ε (-β)).comp
      (Common.dysonCoeff (fermionEnergy ε) V n β))

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
  change PowerSeries.constantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β V) =
    freePartitionFunction ε β
  rw [Common.constantCoeff_dysonTraceSeries, freePartitionFunction]
  congr 1
  funext n
  rw [freeBoltzmannWeight, Common.boltzmannWeight, fermionEnergy]
  push_cast
  ring_nf

omit [LinearOrder Mode] in
@[simp]
theorem dysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    dysonPartitionCoeff ε β V 0 = freePartitionFunction ε β := by
  rw [← coeff_dysonPartitionSeries, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_dysonPartitionSeries]

/-- The normalized logarithm of the fermionic Dyson partition series. -/
noncomputable def dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) : PowerSeries ℂ :=
  PowerSeries.logOf
    (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))

omit [LinearOrder Mode] in
theorem constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    PowerSeries.constantCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) = 1 :=
  PowerSeries.constantCoeff_normalizeByConstantCoeff
    (constantCoeff_dysonPartitionSeries ε β V ▸ freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- The formal logarithm has vanishing constant coefficient. -/
theorem constantCoeff_dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    PowerSeries.constantCoeff (dysonFormalLogPartitionFunction ε β V) = 0 := by
  rw [dysonFormalLogPartitionFunction]
  exact PowerSeries.constantCoeff_logOf
    (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries ε β V)

end Fermionic
end SecondQuantization
