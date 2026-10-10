import LeanCondensedMatter.Models.Parabolic2DEG.Model
import LeanCondensedMatter.Transport.Resolvent.Spectral
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Green functions for the parabolic 2DEG

The clean one-band Hamiltonian and current vertices are owned by `Model`.
This module supplies the model-specific scalar and bounded-operator Green functions through the
generic signed spectral resolvent. Finite positive broadening and probe energy remain explicit.
-/

namespace QuantumTheory.Models.Parabolic2DEG

noncomputable section

open QuantumTheory.Transport

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

end QuantumTheory.Models.Parabolic2DEG
