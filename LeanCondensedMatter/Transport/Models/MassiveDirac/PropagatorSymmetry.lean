import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator

set_option linter.style.header false

/-!
# Momentum-inversion symmetry of the massive-Dirac Green operator

Under simultaneous momentum inversion `(pₓ,pᵧ) ↦ (-pₓ,-pᵧ)`, the arbitrary-regulator quadratic
Green denominator and scalar coefficient are even. The Pauli-vector coefficients have axis-dependent
parity: `σₓ` and `σᵧ` are odd, while `σ_z` is even. Consequently the inversion-symmetrized clean
propagator contains only the `I` and `σ_z` Pauli channels. Physical spectral sides are introduced
only by downstream consumers that need branch semantics.

No integration measure, ultraviolet cutoff, disorder normalization, Born closure, or scattering-rate
limit is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Sign acquired by a Pauli-vector coefficient under simultaneous in-plane momentum inversion. -/
def pauliAxisMomentumInversionSign : PauliAxis → ℝ
  | .x => -1
  | .y => -1
  | .z => 1

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

@[simp] theorem pauliGreenPauliCoefficientOfRegulator_neg_momentum
    (axis : PauliAxis) (v m px py probeEnergy regulator : ℝ) :
    pauliGreenPauliCoefficientOfRegulator
        axis v m (-px) (-py) probeEnergy regulator =
      ((pauliAxisMomentumInversionSign axis : ℝ) : ℂ) *
        pauliGreenPauliCoefficientOfRegulator
          axis v m px py probeEnergy regulator := by
  cases axis <;>
    simp [pauliGreenPauliCoefficientOfRegulator, pauliAxisComponent,
      pauliAxisMomentumInversionSign]

/-- The inversion symmetrization of the arbitrary-regulator Green operator retains only its scalar
and `σ_z` channels. -/
theorem pauliGreenOperatorOfRegulator_add_neg_momentum
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenOperatorOfRegulator v m px py probeEnergy regulator +
        pauliGreenOperatorOfRegulator v m (-px) (-py) probeEnergy regulator =
      (2 : ℂ) •
        (pauliGreenScalarCoefficientOfRegulator v m px py probeEnergy regulator • 1 +
          pauliGreenPauliCoefficientOfRegulator .z v m px py probeEnergy regulator •
            matrixOperator sigmaZ) := by
  simp [pauliGreenOperatorOfRegulator, pauliAxisMomentumInversionSign, two_smul]
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
        pauliGreenPauliCoefficientOfRegulator .z v m px py probeEnergy regulator •
          matrixOperator sigmaZ := by
  unfold inversionSymmetrizedPauliGreenOperatorOfRegulator
  rw [pauliGreenOperatorOfRegulator_add_neg_momentum]
  module

end

end QuantumTheory.Transport.Models.MassiveDirac
