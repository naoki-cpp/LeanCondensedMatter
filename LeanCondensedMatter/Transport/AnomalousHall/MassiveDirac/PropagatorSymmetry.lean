import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator

set_option linter.style.header false

/-!
# Momentum-inversion symmetry of the massive-Dirac Green operator

This Phase 4 bridge isolates the exact algebraic symmetry used before introducing a continuum
momentum integral.  Under simultaneous momentum inversion `(pₓ,pᵧ) ↦ (-pₓ,-pᵧ)`, the quadratic
Green denominator, scalar coefficient, and `σ_z` coefficient are even, while the `σₓ` and `σᵧ`
coefficients are odd.  Consequently the inversion-symmetrized clean propagator contains only the
`I` and `σ_z` Pauli channels.

No integration measure, ultraviolet cutoff, disorder normalization, Born closure, or scattering-rate
limit is introduced here.  A later disorder consumer may combine these exact parity identities with
an inversion-symmetric momentum average.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Simultaneous momentum inversion leaves the massive-Dirac dispersion polynomial unchanged. -/
@[simp] theorem energySq_neg_momentum (v m px py : ℝ) :
    energySq v m (-px) (-py) = energySq v m px py := by
  simp [energySq]

/-- The quadratic Green denominator is even under simultaneous momentum inversion. -/
@[simp] theorem pauliGreenDenominator_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenDenominator side v m (-px) (-py) probeEnergy broadening =
      pauliGreenDenominator side v m px py probeEnergy broadening := by
  simp [pauliGreenDenominator]

/-- The scalar Pauli coefficient is even under simultaneous momentum inversion. -/
@[simp] theorem pauliGreenScalarCoefficient_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenScalarCoefficient side v m (-px) (-py) probeEnergy broadening =
      pauliGreenScalarCoefficient side v m px py probeEnergy broadening := by
  simp [pauliGreenScalarCoefficient]

/-- The `σₓ` Pauli coefficient is odd under simultaneous momentum inversion. -/
@[simp] theorem pauliGreenXCoefficient_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenXCoefficient side v m (-px) (-py) probeEnergy broadening =
      -pauliGreenXCoefficient side v m px py probeEnergy broadening := by
  simp [pauliGreenXCoefficient]

/-- The `σᵧ` Pauli coefficient is odd under simultaneous momentum inversion. -/
@[simp] theorem pauliGreenYCoefficient_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenYCoefficient side v m (-px) (-py) probeEnergy broadening =
      -pauliGreenYCoefficient side v m px py probeEnergy broadening := by
  simp [pauliGreenYCoefficient]

/-- The `σ_z` Pauli coefficient is even under simultaneous momentum inversion. -/
@[simp] theorem pauliGreenZCoefficient_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenZCoefficient side v m (-px) (-py) probeEnergy broadening =
      pauliGreenZCoefficient side v m px py probeEnergy broadening := by
  simp [pauliGreenZCoefficient]

/-- The inversion symmetrization of the clean Green operator retains only its scalar and `σ_z`
channels.  This is the exact algebraic reduction consumed by a later inversion-symmetric momentum
average. -/
theorem pauliGreenOperator_add_neg_momentum
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenOperator side v m px py probeEnergy broadening +
        pauliGreenOperator side v m (-px) (-py) probeEnergy broadening =
      (2 : ℂ) •
        (pauliGreenScalarCoefficient side v m px py probeEnergy broadening • 1 +
          pauliGreenZCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaZ) := by
  simp [pauliGreenOperator, two_smul]
  module

/-- Clean Green operator averaged with its momentum-inverted partner.  This belongs to the exact
propagator-symmetry layer rather than to any disorder closure. -/
noncomputable def inversionSymmetrizedPauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  (1 / 2 : ℂ) •
    (pauliGreenOperator side v m px py probeEnergy broadening +
      pauliGreenOperator side v m (-px) (-py) probeEnergy broadening)

/-- Exact momentum-inversion symmetrization retains only the scalar and `σ_z` Pauli channels. -/
theorem inversionSymmetrizedPauliGreenOperator_eq_evenChannels
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    inversionSymmetrizedPauliGreenOperator side v m px py probeEnergy broadening =
      pauliGreenScalarCoefficient side v m px py probeEnergy broadening • 1 +
        pauliGreenZCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaZ := by
  unfold inversionSymmetrizedPauliGreenOperator
  rw [pauliGreenOperator_add_neg_momentum]
  module

end

end AnomalousHall.MassiveDirac
