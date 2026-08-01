import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannWeight
import LeanCondensedMatter.Analysis.PowerSeries.Normalization

set_option linter.style.header false

/-!
# The fermionic Dyson partition-function series

The statistics-independent coefficient and series are supplied by
`SecondQuantization.Common.Perturbation.DysonTraceSeries`. This file exposes only the genuinely
fermionic specialization and its relation to the free partition function.
-/

namespace SecondQuantization

open PowerSeries

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The fermionic specialization of `Common.dysonTraceSeries`. -/
noncomputable def dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  Common.dysonTraceSeries (fermionEnergy ε) β V

omit [LinearOrder Mode] in
/-- Coefficients are the canonical statistics-independent Dyson trace coefficients. -/
theorem coeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    PowerSeries.coeff n (dysonPartitionSeries ε β V) =
      Common.dysonTraceCoeff (fermionEnergy ε) β V n :=
  Common.coeff_dysonTraceSeries (fermionEnergy ε) β V n

omit [LinearOrder Mode] in
/-- The constant coefficient is the fermionic free partition function. -/
theorem constantCoeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (dysonPartitionSeries ε β V) = freePartitionFunction ε β := by
  change PowerSeries.constantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β V) =
    freePartitionFunction ε β
  rw [Common.constantCoeff_dysonTraceSeries, freePartitionFunction]
  congr 1
  funext n
  exact (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β n).symm

omit [LinearOrder Mode] in
@[simp]
theorem coeff_zero_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.coeff 0 (dysonPartitionSeries ε β V) = freePartitionFunction ε β := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dysonPartitionSeries]

/-- The normalized logarithm of the fermionic Dyson partition series. -/
noncomputable def dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  PowerSeries.logOf
    (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V))

omit [LinearOrder Mode] in
theorem constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) = 1 :=
  PowerSeries.constantCoeff_normalizeByConstantCoeff
    (constantCoeff_dysonPartitionSeries ε β V ▸ freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- The formal logarithm has vanishing constant coefficient. -/
theorem constantCoeff_dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (dysonFormalLogPartitionFunction ε β V) = 0 := by
  rw [dysonFormalLogPartitionFunction]
  exact PowerSeries.constantCoeff_logOf
    (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries ε β V)

end SecondQuantization
