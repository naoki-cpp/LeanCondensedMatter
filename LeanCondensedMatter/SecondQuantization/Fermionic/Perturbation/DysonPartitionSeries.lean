import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonTraceSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannWeight
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.FormalLogPartitionFunction

set_option linter.style.header false

/-!
# The fermionic Dyson partition-function series

The statistics-independent finite Dyson trace coefficient and its formal power series live in
`SecondQuantization.Common.Perturbation.DysonTraceSeries`. This file retains the existing fermionic
partition-function API as a thin specialization at
`Config := FermionOccupation Mode` and `energy := fermionEnergy ε`, and connects the generic
zeroth-order weight sum to `freePartitionFunction`.

All series here are coefficientwise formal power series. No convergence or equality with a genuine
analytic partition function is asserted.
-/

namespace SecondQuantization

open PowerSeries

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The fermionic finite Dyson trace coefficient. Its unfolded form is retained for compatibility
with existing trace-level proofs; it is definitionally equal to `Common.dysonTraceCoeff`. -/
noncomputable def dysonPartitionCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) : ℂ :=
  Common.traceFock ((imaginaryTimeEvolveFree ε (-β)).comp (dysonCoeff ε V n β))

omit [LinearOrder Mode] in
/-- The fermionic coefficient is the specialization of the Common finite Dyson trace coefficient. -/
theorem dysonPartitionCoeff_eq_dysonTraceCoeff (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    dysonPartitionCoeff ε β V n = Common.dysonTraceCoeff (fermionEnergy ε) β V n := rfl

/-- The fermionic specialization of `Common.dysonTraceSeries`. -/
noncomputable def dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  Common.dysonTraceSeries (fermionEnergy ε) β V

omit [LinearOrder Mode] in
theorem coeff_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    PowerSeries.coeff n (dysonPartitionSeries ε β V) = dysonPartitionCoeff ε β V n := by
  rw [dysonPartitionCoeff_eq_dysonTraceCoeff]
  exact Common.coeff_dysonTraceSeries (fermionEnergy ε) β V n

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
theorem dysonPartitionCoeff_zero (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    dysonPartitionCoeff ε β V 0 = freePartitionFunction ε β := by
  rw [← coeff_dysonPartitionSeries, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_dysonPartitionSeries]

/-- The normalized/logarithmic fermionic Dyson partition series. -/
noncomputable def dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) : PowerSeries ℂ :=
  formalLogPartitionFunction (normalizePartitionSeries (dysonPartitionSeries ε β V))

omit [LinearOrder Mode] in
theorem constantCoeff_normalizePartitionSeries_dysonPartitionSeries (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (normalizePartitionSeries (dysonPartitionSeries ε β V)) = 1 :=
  constantCoeff_normalizePartitionSeries
    (constantCoeff_dysonPartitionSeries ε β V ▸ freePartitionFunction_ne_zero ε β)

omit [LinearOrder Mode] in
/-- The formal logarithm has vanishing constant coefficient. -/
theorem constantCoeff_dysonFormalLogPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    PowerSeries.constantCoeff (dysonFormalLogPartitionFunction ε β V) = 0 :=
  constantCoeff_formalLogPartitionFunction
    (constantCoeff_normalizePartitionSeries_dysonPartitionSeries ε β V)

end SecondQuantization
