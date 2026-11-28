import Mathlib.Basic.Real.Basic

set_option linter.style.header false

/-!
# Finite continuum response parameters

Model-independent probe energy, finite momentum cutoff, spectral broadening, signed charge,
and measure normalization. Clean Hamiltonian parameters and model-specific regularity
conditions remain separate.
-/

namespace QuantumTheory
namespace Transport

/-- Common finite continuum response and measure-normalization data. -/
structure FiniteResponseParameters where
  /-- Chemical potential used as the Green-function probe energy. -/
  chemicalPotential : ℝ
  /-- Finite radial physical-momentum cutoff. -/
  momentumCutoff : ℝ
  /-- Retarded/advanced spectral broadening. -/
  broadening : ℝ
  /-- Signed carrier charge in the convention `j = q v`. -/
  signedCharge : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Explicit normalization multiplying the momentum integral. -/
  momentumMeasureNormalization : ℝ

/-- Common physical regularity assumptions for a finite continuum response. -/
structure FiniteResponseParameters.IsRegular (params : FiniteResponseParameters) : Prop where
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff
  broadening_pos : 0 < params.broadening
  hbar_pos : 0 < params.hbar

end Transport
end QuantumTheory
