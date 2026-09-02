import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral

set_option linter.style.header false

/-!
# Pauli decomposition of the massive-Dirac Green operator

This Phase 4 consumer rewrites the existing generic retarded/advanced resolvent of the clean
massive-Dirac Hamiltonian in the Pauli basis needed by the scalar-disorder Born calculation.
For either spectral side `s`, with `z_s = ε + s iη`, the model identity is

```text
G_s = (z_s I - H₀)⁻¹
    = (z_s I + H₀) / (z_s² - E²)
    = g₀ I + gₓ σₓ + gᵧ σᵧ + g_z σ_z.
```

The object identified below is the repository's existing resolvent; this file does not introduce a
parallel Green-function formalism. No disorder data, momentum integration, angular average, Born
closure, SCBA, or vertex resummation is introduced here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Common quadratic denominator `z_s² - E²` of the two-band Green operator. -/
def pauliGreenDenominator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  spectralParameter side probeEnergy broadening ^ 2 -
    ((energySq v m px py : ℝ) : ℂ)

/-- Identity-matrix coefficient in the massive-Dirac Green operator. -/
def pauliGreenScalarCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  (pauliGreenDenominator side v m px py probeEnergy broadening)⁻¹ *
    spectralParameter side probeEnergy broadening

/-- `σₓ` coefficient in the massive-Dirac Green operator. -/
def pauliGreenXCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  (pauliGreenDenominator side v m px py probeEnergy broadening)⁻¹ *
    ((v * px : ℝ) : ℂ)

/-- `σᵧ` coefficient in the massive-Dirac Green operator. -/
def pauliGreenYCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  (pauliGreenDenominator side v m px py probeEnergy broadening)⁻¹ *
    ((v * py : ℝ) : ℂ)

/-- `σ_z` coefficient in the massive-Dirac Green operator. -/
def pauliGreenZCoefficient
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : ℂ :=
  (pauliGreenDenominator side v m px py probeEnergy broadening)⁻¹ *
    ((m : ℝ) : ℂ)

/-- Pauli-basis Green-operator candidate. The theorems below identify it with the existing generic
resolvent at nonzero broadening. -/
noncomputable def pauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  pauliGreenScalarCoefficient side v m px py probeEnergy broadening • 1 +
    pauliGreenXCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaX +
    pauliGreenYCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaY +
    pauliGreenZCoefficient side v m px py probeEnergy broadening • matrixOperator sigmaZ

/-- The bounded massive-Dirac Hamiltonian has the same explicit Pauli decomposition as its matrix
representative. -/
theorem hamiltonianOperator_eq_pauli (v m px py : ℝ) :
    hamiltonianOperator v m px py =
      (((v * px : ℝ) : ℂ)) • matrixOperator sigmaX +
        (((v * py : ℝ) : ℂ)) • matrixOperator sigmaY +
          (((m : ℝ) : ℂ)) • matrixOperator sigmaZ := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (hamiltonian v m px py) =
    (((v * px : ℝ) : ℂ)) • φ sigmaX +
      (((v * py : ℝ) : ℂ)) • φ sigmaY +
        (((m : ℝ) : ℂ)) • φ sigmaZ
  unfold hamiltonian
  rw [map_add, map_add, map_smul, map_smul, map_smul]

/-- Transporting `H₀² = E² I` to `DiracHilbert` gives the bounded-operator square identity used by
the closed resolvent form. -/
theorem hamiltonianOperator_mul_self (v m px py : ℝ) :
    hamiltonianOperator v m px py * hamiltonianOperator v m px py =
      (((energySq v m px py : ℝ) : ℂ)) •
        (1 : DiracHilbert →L[ℂ] DiracHilbert) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (hamiltonian v m px py) * φ (hamiltonian v m px py) = _
  calc
    φ (hamiltonian v m px py) * φ (hamiltonian v m px py) =
        φ (hamiltonian v m px py * hamiltonian v m px py) := by
      symm
      exact map_mul φ _ _
    _ = φ ((((energySq v m px py : ℝ) : ℂ)) • (1 : Matrix2)) := by
      rw [hamiltonian_mul_self]
    _ = (((energySq v m px py : ℝ) : ℂ)) • φ (1 : Matrix2) := by
      exact map_smul φ _ _
    _ = (((energySq v m px py : ℝ) : ℂ)) •
        (1 : DiracHilbert →L[ℂ] DiracHilbert) := by
      rw [map_one]

/-- Nonzero broadening keeps the quadratic two-band denominator away from zero. -/
theorem pauliGreenDenominator_ne_zero
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    pauliGreenDenominator side v m px py probeEnergy broadening ≠ 0 := by
  have hminus := spectralParameter_sub_real_ne_zero
    side probeEnergy broadening (energy v m px py) hbroadening
  have hplus := spectralParameter_sub_real_ne_zero
    side probeEnergy broadening (-energy v m px py) hbroadening
  have hEsq :
      (((energySq v m px py : ℝ) : ℂ)) =
        (((energy v m px py : ℝ) : ℂ)) ^ 2 := by
    norm_cast
    exact (energy_sq v m px py).symm
  unfold pauliGreenDenominator
  rw [hEsq]
  rw [show
    spectralParameter side probeEnergy broadening ^ 2 -
          (((energy v m px py : ℝ) : ℂ)) ^ 2 =
        (spectralParameter side probeEnergy broadening -
            ((energy v m px py : ℝ) : ℂ)) *
          (spectralParameter side probeEnergy broadening +
            ((energy v m px py : ℝ) : ℂ)) by ring]
  exact mul_ne_zero hminus (by simpa using hplus)

/-- The explicit Pauli decomposition is the usual closed numerator/denominator form
`(z_s I + H₀)/(z_s²-E²)`. -/
theorem pauliGreenOperator_eq_closedForm
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    pauliGreenOperator side v m px py probeEnergy broadening =
      (pauliGreenDenominator side v m px py probeEnergy broadening)⁻¹ •
        (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
            (spectralParameter side probeEnergy broadening) +
          hamiltonianOperator v m px py) := by
  rw [hamiltonianOperator_eq_pauli]
  simp [pauliGreenOperator, pauliGreenScalarCoefficient,
    pauliGreenXCoefficient, pauliGreenYCoefficient, pauliGreenZCoefficient,
    Algebra.algebraMap_eq_smul_one, smul_add, smul_smul]
  module

private theorem spectralShift_mul_pauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
          (spectralParameter side probeEnergy broadening) -
        hamiltonianOperator v m px py) *
      pauliGreenOperator side v m px py probeEnergy broadening = 1 := by
  rw [pauliGreenOperator_eq_closedForm]
  rw [mul_smul_comm]
  have hquadratic :
      (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
            (spectralParameter side probeEnergy broadening) -
          hamiltonianOperator v m px py) *
        (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
            (spectralParameter side probeEnergy broadening) +
          hamiltonianOperator v m px py) =
        pauliGreenDenominator side v m px py probeEnergy broadening •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) := by
    rw [sub_mul, mul_add, mul_add]
    rw [hamiltonianOperator_mul_self]
    simp [Algebra.algebraMap_eq_smul_one, pauliGreenDenominator, smul_smul, sub_smul]
    module
  rw [hquadratic, smul_smul]
  simp [pauliGreenDenominator_ne_zero side v m px py probeEnergy broadening hbroadening]

/-- The generic side-indexed resolvent equals the explicit massive-Dirac Pauli decomposition. -/
theorem resolvent_spectralParameter_eq_pauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    resolvent (hamiltonianOperator v m px py)
        (spectralParameter side probeEnergy broadening) =
      pauliGreenOperator side v m px py probeEnergy broadening := by
  apply resolvent_eq_of_spectralShift_mul_eq_one
    side (hamiltonianOperator v m px py)
      (pauliGreenOperator side v m px py probeEnergy broadening)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy broadening hbroadening
  exact spectralShift_mul_pauliGreenOperator
    side v m px py probeEnergy broadening hbroadening

/-- Adjointing the explicit Pauli Green operator exchanges the spectral side. -/
theorem star_pauliGreenOperator
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    star (pauliGreenOperator side v m px py probeEnergy broadening) =
      pauliGreenOperator side.opposite v m px py probeEnergy broadening := by
  have hside :
      spectralResolvent side (hamiltonianOperator v m px py) probeEnergy broadening =
        pauliGreenOperator side v m px py probeEnergy broadening := by
    simpa only [spectralResolvent] using
      resolvent_spectralParameter_eq_pauliGreenOperator side
        v m px py probeEnergy broadening hbroadening
  have hopposite :
      spectralResolvent side.opposite (hamiltonianOperator v m px py) probeEnergy broadening =
        pauliGreenOperator side.opposite v m px py probeEnergy broadening := by
    simpa only [spectralResolvent] using
      resolvent_spectralParameter_eq_pauliGreenOperator side.opposite
        v m px py probeEnergy broadening hbroadening
  rw [← hside, ← hopposite]
  exact star_spectralResolvent side
    (hamiltonianOperator v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    probeEnergy broadening

end

end AnomalousHall.MassiveDirac