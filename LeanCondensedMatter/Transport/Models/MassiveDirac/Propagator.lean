import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral

set_option linter.style.header false

/-!
# Pauli decomposition of the massive-Dirac Green operator

The analytic core is written at an arbitrary signed regulator `γ`,

```text
z = ε + iγ,
G(z) = (z I - H₀)⁻¹
     = (z I + H₀) / (z² - E²)
     = g₀ I + gₓ σₓ + gᵧ σᵧ + g_z σ_z.
```

Physical retarded/advanced branches specialize through the canonical `side.regulator η` boundary.
The object identified below is the repository's existing resolvent; this file does not introduce a
parallel Green-function formalism. No disorder data, momentum integration, angular average, Born
closure, SCBA, or vertex resummation is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Common quadratic denominator `z² - E²` at an arbitrary signed regulator. -/
def pauliGreenDenominatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) : ℂ :=
  spectralParameterOfRegulator probeEnergy regulator ^ 2 -
    ((energySq v m px py : ℝ) : ℂ)

/-- Physical-side specialization of the quadratic Green denominator. -/
def pauliGreenDenominator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  pauliGreenDenominatorOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- Identity-matrix coefficient at an arbitrary signed regulator. -/
def pauliGreenScalarCoefficientOfRegulator
    (v m px py probeEnergy regulator : ℝ) : ℂ :=
  (pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator)⁻¹ *
    spectralParameterOfRegulator probeEnergy regulator

/-- `σₓ` coefficient at an arbitrary signed regulator. -/
def pauliGreenXCoefficientOfRegulator
    (v m px py probeEnergy regulator : ℝ) : ℂ :=
  (pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator)⁻¹ *
    ((v * px : ℝ) : ℂ)

/-- `σᵧ` coefficient at an arbitrary signed regulator. -/
def pauliGreenYCoefficientOfRegulator
    (v m px py probeEnergy regulator : ℝ) : ℂ :=
  (pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator)⁻¹ *
    ((v * py : ℝ) : ℂ)

/-- `σ_z` coefficient at an arbitrary signed regulator. -/
def pauliGreenZCoefficientOfRegulator
    (v m px py probeEnergy regulator : ℝ) : ℂ :=
  (pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator)⁻¹ *
    ((m : ℝ) : ℂ)

/-- Physical-side identity-matrix coefficient. -/
def pauliGreenScalarCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  pauliGreenScalarCoefficientOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- Physical-side `σₓ` coefficient. -/
def pauliGreenXCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  pauliGreenXCoefficientOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- Physical-side `σᵧ` coefficient. -/
def pauliGreenYCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  pauliGreenYCoefficientOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- Physical-side `σ_z` coefficient. -/
def pauliGreenZCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  pauliGreenZCoefficientOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- Pauli-basis Green-operator candidate at an arbitrary signed regulator. -/
noncomputable def pauliGreenOperatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  pauliGreenScalarCoefficientOfRegulator v m px py probeEnergy regulator • 1 +
    pauliGreenXCoefficientOfRegulator v m px py probeEnergy regulator • matrixOperator sigmaX +
    pauliGreenYCoefficientOfRegulator v m px py probeEnergy regulator • matrixOperator sigmaY +
    pauliGreenZCoefficientOfRegulator v m px py probeEnergy regulator • matrixOperator sigmaZ

/-- Physical-side specialization of the Pauli-basis Green operator. -/
noncomputable def pauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  pauliGreenOperatorOfRegulator
    v m px py probeEnergy (side.regulator broadening)

/-- The bounded massive-Dirac Hamiltonian has the same explicit Pauli decomposition as its matrix
representative. -/
theorem hamiltonianOperator_eq_pauli (v m px py : ℝ) :
    hamiltonianOperator v m px py =
      (((v * px : ℝ) : ℂ)) • matrixOperator sigmaX +
        (((v * py : ℝ) : ℂ)) • matrixOperator sigmaY +
          (((m : ℝ) : ℂ)) • matrixOperator sigmaZ := by
  unfold hamiltonianOperator matrixOperator hamiltonian
  rw [map_add, map_add, map_smul, map_smul, map_smul]

/-- Transporting `H₀² = E² I` to `DiracHilbert` gives the bounded-operator square identity used by
the closed resolvent form. -/
theorem hamiltonianOperator_mul_self (v m px py : ℝ) :
    hamiltonianOperator v m px py * hamiltonianOperator v m px py =
      (((energySq v m px py : ℝ) : ℂ)) •
        (1 : DiracHilbert →L[ℂ] DiracHilbert) := by
  unfold hamiltonianOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_self, map_smul, map_one]

/-- A nonzero signed regulator keeps the quadratic two-band denominator away from zero. -/
theorem pauliGreenDenominatorOfRegulator_ne_zero
    (v m px py probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator ≠ 0 := by
  have hminus := spectralParameterOfRegulator_sub_real_ne_zero
    probeEnergy regulator (energy v m px py) hregulator
  have hplus := spectralParameterOfRegulator_sub_real_ne_zero
    probeEnergy regulator (-energy v m px py) hregulator
  have hEsq :
      (((energySq v m px py : ℝ) : ℂ)) =
        (((energy v m px py : ℝ) : ℂ)) ^ 2 := by
    norm_cast
    exact (energy_sq v m px py).symm
  unfold pauliGreenDenominatorOfRegulator
  rw [hEsq]
  rw [show
    spectralParameterOfRegulator probeEnergy regulator ^ 2 -
          (((energy v m px py : ℝ) : ℂ)) ^ 2 =
        (spectralParameterOfRegulator probeEnergy regulator -
            ((energy v m px py : ℝ) : ℂ)) *
          (spectralParameterOfRegulator probeEnergy regulator +
            ((energy v m px py : ℝ) : ℂ)) by ring]
  exact mul_ne_zero hminus (by simpa using hplus)

/-- The inverse radial Green denominator is continuous for every nonzero signed regulator. -/
theorem continuous_inv_pauliGreenDenominatorOfRegulator_radial
    (v m probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (fun p : ℝ =>
      (pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator)⁻¹) := by
  have hden : Continuous (fun p : ℝ =>
      pauliGreenDenominatorOfRegulator v m p 0 probeEnergy regulator) := by
    unfold pauliGreenDenominatorOfRegulator energySq spectralParameterOfRegulator
    fun_prop
  exact hden.inv₀ (fun p =>
    pauliGreenDenominatorOfRegulator_ne_zero
      v m p 0 probeEnergy regulator hregulator)

/-- The arbitrary-regulator Pauli decomposition is the usual closed numerator/denominator form. -/
theorem pauliGreenOperatorOfRegulator_eq_closedForm
    (v m px py probeEnergy regulator : ℝ) :
    pauliGreenOperatorOfRegulator v m px py probeEnergy regulator =
      (pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator)⁻¹ •
        (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
            (spectralParameterOfRegulator probeEnergy regulator) +
          hamiltonianOperator v m px py) := by
  rw [hamiltonianOperator_eq_pauli]
  simp [pauliGreenOperatorOfRegulator, pauliGreenScalarCoefficientOfRegulator,
    pauliGreenXCoefficientOfRegulator, pauliGreenYCoefficientOfRegulator,
    pauliGreenZCoefficientOfRegulator, Algebra.algebraMap_eq_smul_one, smul_add, smul_smul]
  module

private theorem spectralShift_mul_pauliGreenOperatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
          (spectralParameterOfRegulator probeEnergy regulator) -
        hamiltonianOperator v m px py) *
      pauliGreenOperatorOfRegulator v m px py probeEnergy regulator = 1 := by
  have hdenEq :
      spectralParameterOfRegulator probeEnergy regulator ^ 2 -
          (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 - (((m : ℝ) : ℂ)) ^ 2 =
        pauliGreenDenominatorOfRegulator v m px py probeEnergy regulator := by
    unfold pauliGreenDenominatorOfRegulator energySq
    push_cast
    ring
  have hden :
      spectralParameterOfRegulator probeEnergy regulator ^ 2 -
          (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 - (((m : ℝ) : ℂ)) ^ 2 ≠ 0 := by
    rw [hdenEq]
    exact pauliGreenDenominatorOfRegulator_ne_zero
      v m px py probeEnergy regulator hregulator
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  have hmatrix := congrArg matrixOperator
    (pauliShiftMatrix_mul_closedInverse
      (spectralParameterOfRegulator probeEnergy regulator)
      (((v * px : ℝ) : ℂ)) (((v * py : ℝ) : ℂ)) (((m : ℝ) : ℂ)) hden)
  change φ
      ((spectralParameterOfRegulator probeEnergy regulator • (1 : Matrix2) -
          (((v * px : ℝ) : ℂ)) • sigmaX - (((v * py : ℝ) : ℂ)) • sigmaY -
          (((m : ℝ) : ℂ)) • sigmaZ) *
        ((spectralParameterOfRegulator probeEnergy regulator ^ 2 -
          (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 - (((m : ℝ) : ℂ)) ^ 2)⁻¹ •
          (spectralParameterOfRegulator probeEnergy regulator • (1 : Matrix2) +
            (((v * px : ℝ) : ℂ)) • sigmaX + (((v * py : ℝ) : ℂ)) • sigmaY +
            (((m : ℝ) : ℂ)) • sigmaZ))) = φ 1 at hmatrix
  simp only [map_mul, map_add, map_sub, map_smul, map_one] at hmatrix
  rw [pauliGreenOperatorOfRegulator_eq_closedForm, ← hdenEq, hamiltonianOperator_eq_pauli,
    Algebra.algebraMap_eq_smul_one]
  change
    (spectralParameterOfRegulator probeEnergy regulator • 1 -
        ((((v * px : ℝ) : ℂ)) • φ sigmaX + (((v * py : ℝ) : ℂ)) • φ sigmaY +
          (((m : ℝ) : ℂ)) • φ sigmaZ)) *
      ((spectralParameterOfRegulator probeEnergy regulator ^ 2 -
        (((v * px : ℝ) : ℂ)) ^ 2 - (((v * py : ℝ) : ℂ)) ^ 2 - (((m : ℝ) : ℂ)) ^ 2)⁻¹ •
        (spectralParameterOfRegulator probeEnergy regulator • 1 +
          (((v * px : ℝ) : ℂ)) • φ sigmaX + (((v * py : ℝ) : ℂ)) • φ sigmaY +
          (((m : ℝ) : ℂ)) • φ sigmaZ)) = 1
  have hshift :
      spectralParameterOfRegulator probeEnergy regulator •
            (1 : DiracHilbert →L[ℂ] DiracHilbert) -
          ((((v * px : ℝ) : ℂ)) • φ sigmaX + (((v * py : ℝ) : ℂ)) • φ sigmaY +
            (((m : ℝ) : ℂ)) • φ sigmaZ) =
        spectralParameterOfRegulator probeEnergy regulator • 1 -
          (((v * px : ℝ) : ℂ)) • φ sigmaX - (((v * py : ℝ) : ℂ)) • φ sigmaY -
          (((m : ℝ) : ℂ)) • φ sigmaZ := by
    module
  rw [hshift]
  exact hmatrix

/-- The resolvent at an arbitrary nonzero signed regulator equals the explicit Pauli Green operator. -/
theorem resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent (hamiltonianOperator v m px py)
        (spectralParameterOfRegulator probeEnergy regulator) =
      pauliGreenOperatorOfRegulator v m px py probeEnergy regulator := by
  exact resolvent_eq_of_spectralShift_mul_eq_one
    (hamiltonianOperator v m px py)
    (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    probeEnergy regulator hregulator
    (spectralShift_mul_pauliGreenOperatorOfRegulator
      v m px py probeEnergy regulator hregulator)

/-- Adjointing the explicit Pauli Green operator reverses the signed regulator. -/
theorem star_pauliGreenOperatorOfRegulator
    (v m px py probeEnergy regulator : ℝ) (hregulator : regulator ≠ 0) :
    star (pauliGreenOperatorOfRegulator v m px py probeEnergy regulator) =
      pauliGreenOperatorOfRegulator v m px py probeEnergy (-regulator) := by
  have hreg := resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
    v m px py probeEnergy regulator hregulator
  have hneg := resolvent_spectralParameterOfRegulator_eq_pauliGreenOperatorOfRegulator
    v m px py probeEnergy (-regulator) (neg_ne_zero.mpr hregulator)
  rw [← hreg, ← hneg]
  exact star_resolvent_spectralParameterOfRegulator
    (hamiltonianOperator v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    probeEnergy regulator

end

end AnomalousHall.MassiveDirac
