import LeanCondensedMatter.Models.RashbaExchange.Model

set_option linter.style.header false

/-!
# Finite-response parameters for the Rashba-exchange model

The clean Hamiltonian, spectrum, and Berry curvature are owned by `Model` and depend only
on `HamiltonianParameters`. This module owns the additional finite-response parameters,
their regularity conditions, and the finite momentum disk. The signed charge convention is
`j = q v` (with negative `q` for electrons); its current operator is defined downstream
in `Operator`. Occupation laws can be supplied through the generic
`QuantumTheory.bandStateOccupation` interface.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

/-- The Hamiltonian parameters together with finite response and normalization data. -/
structure Parameters extends HamiltonianParameters where
  /-- Chemical potential used as the Green-function probe energy. -/
  chemicalPotential : ℝ
  /-- Finite radial physical-momentum cutoff. -/
  momentumCutoff : ℝ
  /-- Positive retarded/advanced spectral broadening. -/
  broadening : ℝ
  /-- Signed carrier charge in the convention j = q v. -/
  signedCharge : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Explicit normalization multiplying the two-dimensional momentum integral. -/
  momentumMeasureNormalization : ℝ

/-- Forget the response/normalization conditions, retaining the clean Hamiltonian data. -/
instance : Coe Parameters HamiltonianParameters where
  coe params := params.toHamiltonianParameters

/-- Regular finite-parameter regime used by analytic statements about the benchmark. -/
structure Parameters.IsRegular (params : Parameters) : Prop where
  effectiveMass_pos : 0 < params.effectiveMass
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff
  broadening_pos : 0 < params.broadening
  hbar_pos : 0 < params.hbar

/-- Membership in the finite closed momentum disk. -/
def inMomentumDomain (params : Parameters) (px py : ℝ) : Prop :=
  px ^ 2 + py ^ 2 ≤ params.momentumCutoff ^ 2


end
end QuantumTheory.Models.RashbaExchange
