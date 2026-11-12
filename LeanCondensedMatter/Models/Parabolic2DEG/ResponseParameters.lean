import LeanCondensedMatter.Models.Parabolic2DEG.Model

set_option linter.style.header false

/-!
# Finite-response parameters for the parabolic two-dimensional electron gas

The clean Hamiltonian depends only on the effective mass in `Model`. This module owns the
extended finite-response parameter bundle and its regularity predicate. The momentum cutoff
is stored explicitly in the response parameters; spectral broadening, charge and continuum
normalization are not assumptions of the clean Hamiltonian.
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

end

end QuantumTheory.Models.Parabolic2DEG
