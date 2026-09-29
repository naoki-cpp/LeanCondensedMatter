import LeanCondensedMatter.Transport.Analysis.FourierGeometry
import LeanCondensedMatter.Transport.Resolvent.Spectral
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

The benchmark uses physical momentum rather than wave vector and keeps the signed carrier charge,
reduced Planck constant, finite radial momentum cutoff, finite spectral broadening, and
momentum-measure normalization explicit. No infinite-volume, cutoff-removal, zero-broadening, or
universal-limit identification is made here.

The current convention is `j = q v`, where `q` is the signed carrier charge stored in
`Parameters.signedCharge`. In particular an electron convention is represented by a negative
`signedCharge`; no additional minus sign is inserted downstream. The parabolic effective-mass
dispersion is the standard continuum benchmark convention; all normalization choices remain
explicit rather than being inferred from that dispersion.
-/

namespace QuantumTheory.Transport.Models.Parabolic2DEG

noncomputable section

open QuantumTheory.Transport

/-- Physical and measure-normalization data needed to interpret one finite parabolic-2DEG
calculation. Response normalization is deliberately not stored here; the response layer attaches
its named Kubo/Středa prefactor before constructing a physical conductivity tensor. -/
structure Parameters where
  /-- Effective mass `m_eff` in the parabolic dispersion. -/
  effectiveMass : ℝ
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
def bandEnergy (params : Parameters) (px py : ℝ) : ℝ :=
  momentumSq px py / (2 * params.effectiveMass)

/-- Cartesian group-velocity component `v_i = p_i / m_eff`. -/
def velocityComponent
    (params : Parameters) (direction : Fin 2) (px py : ℝ) : ℝ :=
  momentumComponent direction px py / params.effectiveMass

/-- Cartesian electrical-current component in the explicit convention `j_i = q v_i`. -/
def currentComponent
    (params : Parameters) (direction : Fin 2) (px py : ℝ) : ℝ :=
  params.signedCharge * velocityComponent params direction px py

/-- One-band Hamiltonian operator, represented as scalar multiplication on `ℂ`. -/
noncomputable def hamiltonianOperator
    (params : Parameters) (px py : ℝ) : BandHilbert →L[ℂ] BandHilbert :=
  (((bandEnergy params px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

/-- One-band velocity operator represented by the named velocity component. -/
noncomputable def velocityOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
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
    (params : Parameters) (px py : ℝ) :
    IsSelfAdjoint (hamiltonianOperator params px py) := by
  simp [hamiltonianOperator, isSelfAdjoint_iff]

/-- The velocity operator is self-adjoint because its scalar coefficient is real. -/
theorem velocityOperator_isSelfAdjoint
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    IsSelfAdjoint (velocityOperator params direction px py) := by
  simp [velocityOperator, isSelfAdjoint_iff]

/-- The current operator is self-adjoint because the signed charge and velocity are real. -/
theorem currentOperator_isSelfAdjoint
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    IsSelfAdjoint (currentOperator params direction px py) := by
  simp [currentOperator, isSelfAdjoint_iff]

/-- Scalar denominator of the side-indexed one-band Green function. -/
def greenDenominator
    (side : SpectralSide) (params : Parameters) (px py : ℝ) : ℂ :=
  spectralParameter side params.chemicalPotential params.broadening -
    ((bandEnergy params px py : ℝ) : ℂ)

/-- Scalar one-band Green function `Gˢ = (zˢ - ε(p))⁻¹`. -/
def greenScalar
    (side : SpectralSide) (params : Parameters) (px py : ℝ) : ℂ :=
  (greenDenominator side params px py)⁻¹

/-- Canonical operator-valued Green function through the common transport resolvent boundary. -/
noncomputable def greenOperator
    (side : SpectralSide) (params : Parameters) (px py : ℝ) :
    BandHilbert →L[ℂ] BandHilbert :=
  spectralResolvent side (hamiltonianOperator params px py)
    params.chemicalPotential params.broadening

/-- Finite nonzero broadening keeps the scalar Green denominator away from zero. -/
theorem greenDenominator_ne_zero
    (side : SpectralSide) (params : Parameters) (px py : ℝ)
    (hbroadening : params.broadening ≠ 0) :
    greenDenominator side params px py ≠ 0 := by
  simpa [greenDenominator, spectralParameter] using
    spectralParameterOfRegulator_sub_real_ne_zero
      params.chemicalPotential (side.regulator params.broadening)
      (bandEnergy params px py) (side.regulator_ne_zero hbroadening)

/-- The canonical operator Green function acts by the named scalar Green factor. This is the
explicit bridge that lets response code use scalar one-band algebra without bypassing the common
resolvent boundary. -/
theorem greenOperator_apply
    (side : SpectralSide) (params : Parameters) (px py : ℝ)
    (hbroadening : params.broadening ≠ 0) (ψ : BandHilbert) :
    greenOperator side params px py ψ = greenScalar side params px py • ψ := by
  have heigen :
      hamiltonianOperator params px py ψ =
        (((bandEnergy params px py : ℝ) : ℂ)) • ψ := by
    simp [hamiltonianOperator]
  simpa [greenOperator, spectralResolvent, spectralParameter,
    greenScalar, greenDenominator] using
    (resolvent_spectralParameterOfRegulator_apply_eigenvector
      (hamiltonianOperator params px py)
      (hamiltonianOperator_isSelfAdjoint params px py)
      heigen
      params.chemicalPotential
      (side.regulator params.broadening)
      (side.regulator_ne_zero hbroadening))

/-- Operator/scalar Green bridge for the one-band model. -/
theorem greenOperator_eq_greenScalar_smul_id
    (side : SpectralSide) (params : Parameters) (px py : ℝ)
    (hbroadening : params.broadening ≠ 0) :
    greenOperator side params px py =
      greenScalar side params px py • (1 : BandHilbert →L[ℂ] BandHilbert) := by
  apply ContinuousLinearMap.ext
  intro ψ
  rw [greenOperator_apply side params px py hbroadening]
  simp

/-- The radial scalar Green function is continuous at every finite nonzero broadening. -/
theorem continuous_greenScalar_radial
    (side : SpectralSide) (params : Parameters)
    (hbroadening : params.broadening ≠ 0) :
    Continuous (fun p : ℝ => greenScalar side params p 0) := by
  have hden :
      Continuous (fun p : ℝ => greenDenominator side params p 0) := by
    unfold greenDenominator bandEnergy momentumSq momentumSq2D spectralParameter
    fun_prop
  exact hden.inv₀ (fun p =>
    greenDenominator_ne_zero side params p 0 hbroadening)

end

end QuantumTheory.Transport.Models.Parabolic2DEG
