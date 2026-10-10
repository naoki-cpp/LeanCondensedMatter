import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite parabolic two-dimensional electron gas

This module owns the finite-parameter model boundary for an isotropic parabolic two-dimensional
electron gas,

```text
ε(p) = |p|² / (2 m_eff).
```

The clean band and velocity use only `HamiltonianParameters` (the effective mass). The
extended `Parameters` carries charge, chemical potential, reduced Planck constant, momentum cutoff,
spectral broadening and measure normalization for finite response calculations. Green functions
live in the separate `Green` module. No infinite-volume, cutoff-removal, zero-broadening, or
universal-limit identification is made here.

The current convention is `j = q v`, where `q` is the signed carrier charge stored in
`Parameters.signedCharge`. In particular an electron convention is represented by a negative
`signedCharge`; no additional minus sign is inserted downstream. The parabolic effective-mass
dispersion is the standard continuum benchmark convention; all normalization choices remain
explicit rather than being inferred from that dispersion.
-/

namespace QuantumTheory.Models.Parabolic2DEG

noncomputable section

open QuantumTheory.Transport

/-- Effective mass determining the clean parabolic band, Hamiltonian and group velocity. -/
structure HamiltonianParameters where
  /-- Effective mass `m_eff` in the parabolic dispersion. -/
  effectiveMass : ℝ

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

/-- The one-band Hilbert space used by the scalar parabolic benchmark. -/
abbrev BandHilbert := ℂ

/-- Cartesian momentum component selected by a coordinate in `Fin 2`. -/
def momentumComponent (direction : Fin 2) (px py : ℝ) : ℝ :=
  if direction = 0 then px else py

/-- Backward-compatible model-local name for the common two-dimensional momentum square. -/
def momentumSq (px py : ℝ) : ℝ :=
  momentumSq2D px py

/-- Finite radial momentum domain encoded by the cutoff stored in `params`. -/
def MomentumInDomain (params : Parameters) (px py : ℝ) : Prop :=
  momentumSq px py ≤ params.momentumCutoff ^ 2

/-- Parabolic band energy `ε(p) = |p|² / (2 m_eff)`. -/
def bandEnergy (params : HamiltonianParameters) (px py : ℝ) : ℝ :=
  momentumSq px py / (2 * params.effectiveMass)

/-- Cartesian group-velocity component `v_i = p_i / m_eff`. -/
def velocityComponent
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) : ℝ :=
  momentumComponent direction px py / params.effectiveMass

/-- Cartesian electrical-current component in the explicit convention `j_i = q v_i`. -/
def currentComponent
    (params : Parameters) (direction : Fin 2) (px py : ℝ) : ℝ :=
  params.signedCharge * velocityComponent params direction px py

/-- One-band Hamiltonian operator, represented as scalar multiplication on `ℂ`. -/
noncomputable def hamiltonianOperator
    (params : HamiltonianParameters) (px py : ℝ) : BandHilbert →L[ℂ] BandHilbert :=
  (((bandEnergy params px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- One-band velocity operator represented by the named velocity component. -/
noncomputable def velocityOperator
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    BandHilbert →L[ℂ] BandHilbert :=
  (((velocityComponent params direction px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- One-band current operator, represented as scalar multiplication by the named current component. -/
noncomputable def currentOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    BandHilbert →L[ℂ] BandHilbert :=
  (((currentComponent params direction px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- The bounded current vertex is the signed carrier charge multiplying the bounded velocity. -/
@[simp]
theorem currentOperator_eq_charge_smul_velocityOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    currentOperator params direction px py =
      (((params.signedCharge : ℝ) : ℂ)) • velocityOperator params direction px py := by
  unfold currentOperator velocityOperator currentComponent
  push_cast
  module

/-- The Hamiltonian operator is self-adjoint because its scalar coefficient is real. -/
theorem hamiltonianOperator_isSelfAdjoint
    (params : HamiltonianParameters) (px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator params px py) := by
  simp [hamiltonianOperator, isSelfAdjoint_iff]

/-- The velocity operator is self-adjoint because its scalar coefficient is real. -/
theorem velocityOperator_isSelfAdjoint
    (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) :
    IsSelfAdjoint (velocityOperator params direction px py) := by
  simp [velocityOperator, isSelfAdjoint_iff]

/-- The current operator is self-adjoint because the signed charge and velocity are real. -/
theorem currentOperator_isSelfAdjoint
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    IsSelfAdjoint (currentOperator params direction px py) := by
  simp [currentOperator, isSelfAdjoint_iff]


end

end QuantumTheory.Models.Parabolic2DEG
