import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.Green.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Radial retarded-advanced Pauli coefficient algebra

The on-axis Pauli data and finite-broadening retarded/advanced coefficient
products of the Born-Dyson Green function. These algebraic transport
identities depend on the Green-function core but are not required to
define its matrix or bounded operator.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Nonzero Pauli coefficients of the Born-Dyson Green propagator on the radial
momentum axis `(p, 0)`. The remaining Pauli-y coefficient vanishes on this axis. -/
structure FiniteCutoffBornDysonRadialPauliData where
  /-- Coefficient of the identity matrix in the radial Green propagator. -/
  scalar : ℂ
  /-- Coefficient of the momentum-axis Pauli matrix `σₓ`. -/
  x : ℂ
  /-- Coefficient of the mass-axis Pauli matrix `σ_z`. -/
  z : ℂ

/-- Scalar, in-plane, and mass-axis Pauli coefficients of a radial Born-Dyson Green
propagator at fixed spectral side, momentum, cutoff, and broadening. -/
noncomputable def finiteCutoffContinuumBornDysonRadialPauliData
    (side : SpectralSide)
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    FiniteCutoffBornDysonRadialPauliData where
  scalar := finiteCutoffContinuumBornDysonScalarCoefficient
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  x := finiteCutoffContinuumBornDysonPauliCoefficient .x
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax
  z := finiteCutoffContinuumBornDysonPauliCoefficient .z
    side v m p 0 probeEnergy broadening disorderStrength hbar pMax

/-- At fixed finite broadening and cutoff, the radial RA scalar-minus-mass
coefficient product has the common physical Dyson denominator. This is a
pointwise algebraic identity; no denominator nonvanishing or regulator limit
is assumed. -/
theorem finiteCutoffContinuumBornDysonRadial_ra_scalar_sub_z_product_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonScalarCoefficient
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonScalarCoefficient
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax -
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonPauliCoefficient .z
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax =
      (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        (finiteCutoffContinuumBornEffectiveEnergy
            .advanced v m probeEnergy broadening disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveEnergy
            .retarded v m probeEnergy broadening disorderStrength hbar pMax -
          finiteCutoffContinuumBornEffectiveMass
            .advanced v m probeEnergy broadening disorderStrength hbar pMax *
          finiteCutoffContinuumBornEffectiveMass
            .retarded v m probeEnergy broadening disorderStrength hbar pMax) := by
  simp only [finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent,
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul,
    mul_inv_rev]
  ring

/-- The radial RA in-plane Pauli product has the same common Dyson
denominator and its numerator is the squared Dirac momentum. -/
theorem finiteCutoffContinuumBornDysonRadial_ra_x_product_eq
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonPauliCoefficient .x
        .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax *
      finiteCutoffContinuumBornDysonPauliCoefficient .x
        .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax =
      (finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
        v m p probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        (((v * p : ℝ) : ℂ) ^ 2) := by
  simp only [finiteCutoffContinuumBornDysonPauliCoefficient,
    InternalSpace.pauliAxisComponent,
    finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct_eq_mul,
    mul_inv_rev]
  push_cast
  ring

end

end QuantumTheory.Models.MassiveDirac
