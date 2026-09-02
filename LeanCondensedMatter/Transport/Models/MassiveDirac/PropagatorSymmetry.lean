import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator

set_option linter.style.header false

/-!
# Momentum-inversion symmetry of the massive-Dirac Green operator

Under simultaneous momentum inversion `(pₓ,pᵧ) ↦ (-pₓ,-pᵧ)`, the arbitrary-regulator quadratic
Green denominator, scalar coefficient, and `σ_z` coefficient are even, while the `σₓ` and `σᵧ`
coefficients are odd. Consequently the inversion-symmetrized clean propagator contains only the
`I` and `σ_z` Pauli channels. Physical spectral sides remain thin specializations of the signed
regulator.

No integration measure, ultraviolet cutoff, disorder normalization, Born closure, or scattering-rate
limit is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Simultaneous momentum inversion leaves the massive-Dirac dispersion polynomial unchanged. -/
@[simp] theorem energySq_neg_momentum (v m px py : ℝ) :
    energySq v m (-px) (-py) = energySq v m px py := by
  simp [energySq]

@[simp] theorem pauliGreenDenominatorOfRegulator_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenDenominatorOfRegulator v m (-px) (-py) probeEnergy regulator =
      pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator := by
  simp [pauliGreenDenominatorOfRegulator]

@[simp] theorem pauliGreenScalarCoefficientOfRegulator_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenScalarCoefficientOfRegulator v m (-px) (-py) probeEnergy regulator =
      pauliGreenScalarCoefficientOfRegulator v m px py probeEnergy regulator := by
  simp [pauliGreenScalarCoefficientOfRegulator]

@[simp] theorem pauliGreenXCoefficientOfRegulator_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenXCoefficientOfRegulator v m (-px) (-py) probeEnergy regulator =
      -pauliGreenXCoefficientOfRegulator v m px py probeEnergy regulator := by
  simp [pauliGreenXCoefficientOfRegulator]

@[simp] theorem pauliGreenYCoefficientOfRegulator_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenYCoefficientOfRegulator v m (-px) (-py) probeEnergy regulator =
      -pauliGreenYCoefficientOfRegulator v m px py probeEnergy regulator := by
  simp [pauliGreenYCoefficientOfRegulator]

@[simp] theorem pauliGreenZCoefficientOfRegulator_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenZCoefficientOfRegulator v m (-px) (-py) probeEnergy regulator =
      pauliGreenZCoefficientOfRegulator v m px py probeEnergy regulator := by
  simp [pauliGreenZCoefficientOfRegulator]

/-- The inversion symmetrization of the arbitrary-regulator Green operator retains only its scalar
and `σ_z` channels. -/
theorem pauliGreenOperatorOfRegulator_add_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenOperatorOfRegulator v m px py probeEnergy regulator +
        pauliGreenOperatorOfRegulator v m (-px) (-py) probeEnergy regulator =
      (2 : ℂ) •
        (pauliGreenScalarCoefficientOfRegulator v m px py probeEnergy regulator • 1 +
          pauliGreenZCoefficientOfRegulator v m px py probeEnergy regulator •
            matrixOperator sigmaZ) := by
  simp [pauliGreenOperatorOfRegulator, two_smul]
  module

/-- Clean Green operator at arbitrary regulator averaged with its momentum-inverted partner. -/
noncomputable def inversionSymmetrizedPauliGreenOperatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  (1 / 2 : ℂ) •
    (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator +
      pauliGreenOperatorOfRegulator v m (-px) (-py) probeEnergy regulator)

/-- Exact arbitrary-regulator momentum-inversion symmetrization retains only the scalar and `σ_z`
Pauli channels. -/
theorem inversionSymmetrizedPauliGreenOperatorOfRegulator_eq_evenChannels
    (v m px py probeEnergy regulator : ℝ) :
    inversionSymmetrizedPauliGreenOperatorOfRegulator v m px py probeEnergy regulator =
      pauliGreenScalarCoefficientOfRegulator v m px py probeEnergy regulator • 1 +
        pauliGreenZCoefficientOfRegulator v m px py probeEnergy regulator •
          matrixOperator sigmaZ := by
  unfold inversionSymmetrizedPauliGreenOperatorOfRegulator
  rw [pauliGreenOperatorOfRegulator_add_neg_momentum]
  module

end

end AnomalousHall.MassiveDirac
