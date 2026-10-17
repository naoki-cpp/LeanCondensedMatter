import LeanCondensedMatter.Models.Parabolic2DEG.Model

set_option linter.style.header false

/-!
# Finite-response parameters for the parabolic two-dimensional electron gas

The clean Hamiltonian depends only on the effective mass in `Model`. This module owns the
extended finite-response parameter bundle, its regularity predicate, and the explicit finite
radial momentum domain. Spectral broadening, charge and continuum normalization are not
assumptions of the clean Hamiltonian.
-/

namespace QuantumTheory.Models.Parabolic2DEG

noncomputable section

/-- Clean model parameters together with the finite response and measure-normalization data.
The Kubo/Středa conductivity prefactor is attached by the response layer, not stored here. -/
structure Parameters extends HamiltonianParameters where
  /-- Chemical potential used as the probe energy of the one-band Green function. -/
  chemicalPotential : ℝ
  /-- Finite radial momentum cutoff `p_max`. -/
  momentumCutoff : ℝ
  /-- Positive-width parameter `η` used by retarded/advanced Green functions. -/
  broadening : ℝ
  /-- Signed carrier charge `q`; the model current convention is `j = q v`. -/
  signedCharge : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Scalar multiplying the radial/angular momentum integral. This records the chosen measure
  normalization explicitly; for physical momentum one may choose `1 / (2πℏ)²`. -/
  momentumMeasureNormalization : ℝ

/-- Use a response parameter bundle where only clean Hamiltonian data is needed. -/
instance : Coe Parameters HamiltonianParameters where
  coe params := params.toHamiltonianParameters

/-- Explicit physical regularity domain for the finite benchmark. -/
structure Parameters.IsRegular (params : Parameters) : Prop where
  effectiveMass_pos : 0 < params.effectiveMass
  broadening_pos : 0 < params.broadening
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff
  hbar_pos : 0 < params.hbar

namespace Parameters.IsRegular

theorem effectiveMass_ne_zero {params : Parameters} (h : params.IsRegular) :
    params.effectiveMass ≠ 0 :=
  ne_of_gt h.effectiveMass_pos

theorem broadening_ne_zero {params : Parameters} (h : params.IsRegular) :
    params.broadening ≠ 0 :=
  ne_of_gt h.broadening_pos

theorem hbar_ne_zero {params : Parameters} (h : params.IsRegular) :
    params.hbar ≠ 0 :=
  ne_of_gt h.hbar_pos

end Parameters.IsRegular

/-- Finite radial momentum domain encoded by the cutoff stored in `params`. -/
def MomentumInDomain (params : Parameters) (px py : ℝ) : Prop :=
  px ^ 2 + py ^ 2 ≤ params.momentumCutoff ^ 2

end

end QuantumTheory.Models.Parabolic2DEG
