import LeanCondensedMatter.Transport.Resolvent.Basic
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

The benchmark keeps the signed carrier charge, reduced Planck constant, finite radial momentum
cutoff, finite spectral broadening, momentum-measure normalization, and final response
normalization explicit. No infinite-volume, cutoff-removal, zero-broadening, or universal-limit
identification is made here.

The current convention is `j = q v`, where `q` is the signed carrier charge stored in
`Parameters.signedCharge`. In particular an electron convention is represented by a negative
`signedCharge`; no additional minus sign is inserted downstream.
-/

namespace QuantumTheory.Transport.Models.Parabolic2DEG

noncomputable section

open QuantumTheory.Transport

/-- Physical and normalization data needed to interpret one finite parabolic-2DEG calculation. -/
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
  /-- Reduced Planck constant used when comparing Drude and Kubo normalizations. -/
  hbar : ℝ
  /-- Scalar multiplying the radial/angular momentum integral. This records the chosen measure
  normalization explicitly; for physical momentum one may choose `1 / (2πℏ)²`. -/
  momentumMeasureNormalization : ℝ
  /-- Remaining scalar response normalization applied after the momentum integral. -/
  responseNormalization : ℝ

/-- Explicit regularity domain for the physical interpretation of the finite benchmark. -/
structure Parameters.IsRegular (params : Parameters) : Prop where
  effectiveMass_ne_zero : params.effectiveMass ≠ 0
  broadening_ne_zero : params.broadening ≠ 0
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff

/-- The one-band Hilbert space used by the scalar parabolic benchmark. -/
abbrev BandHilbert := ℂ

/-- Cartesian momentum component selected by a coordinate in `Fin 2`. -/
def momentumComponent (direction : Fin 2) (px py : ℝ) : ℝ :=
  if direction = 0 then px else py

/-- Squared in-plane momentum `|p|² = p_x² + p_y²`. -/
def momentumSq (px py : ℝ) : ℝ :=
  px ^ 2 + py ^ 2

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

/-- One-band current operator, represented as scalar multiplication by the named current component. -/
noncomputable def currentOperator
    (params : Parameters) (direction : Fin 2) (px py : ℝ) :
    BandHilbert →L[ℂ] BandHilbert :=
  (((currentComponent params direction px py : ℝ) : ℂ)) •
    (1 : BandHilbert →L[ℂ] BandHilbert)

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

/-- The radial scalar Green function is continuous at every finite nonzero broadening. -/
theorem continuous_greenScalar_radial
    (side : SpectralSide) (params : Parameters)
    (hbroadening : params.broadening ≠ 0) :
    Continuous (fun p : ℝ => greenScalar side params p 0) := by
  have hden :
      Continuous (fun p : ℝ => greenDenominator side params p 0) := by
    unfold greenDenominator bandEnergy momentumSq spectralParameter
    fun_prop
  exact hden.inv₀ (fun p =>
    greenDenominator_ne_zero side params p 0 hbroadening)

end

end QuantumTheory.Transport.Models.Parabolic2DEG
