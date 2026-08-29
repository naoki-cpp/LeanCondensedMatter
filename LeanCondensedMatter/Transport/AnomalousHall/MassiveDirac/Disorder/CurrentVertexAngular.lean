import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.AngularReduction
import LeanCondensedMatter.Transport.Disorder.Ladder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Angular reduction of the massive-Dirac retarded-advanced current rung

This Phase 5 entry point keeps the retarded-advanced orientation used by the shared finite ladder
API visible while performing only the model-specific `2 × 2` Pauli algebra.  At fixed radial
momentum it studies

```text
Gᴿ(p,θ) σₓ Gᴬ(p,θ)
```

before any radial integration, disorder normalization, zero-broadening limit, or ladder
resummation.  The full polar-angle integral closes in the in-plane Pauli span.  Reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` term, so the order is not hidden by
a symmetric wrapper.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

/-- Matrix representative of the already-defined Pauli Green operator.  This is only a finite
matrix adapter for explicit Pauli multiplication; it does not introduce a second Green-function
formalism. -/
def pauliGreenMatrix
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) : Matrix2 :=
  pauliGreenScalarCoefficient side v m px py probeEnergy broadening • (1 : Matrix2) +
    pauliGreenXCoefficient side v m px py probeEnergy broadening • sigmaX +
    pauliGreenYCoefficient side v m px py probeEnergy broadening • sigmaY +
    pauliGreenZCoefficient side v m px py probeEnergy broadening • sigmaZ

/-- The matrix representative transports exactly to the canonical bounded Pauli Green operator. -/
theorem matrixOperator_pauliGreenMatrix
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ) :
    matrixOperator (pauliGreenMatrix side v m px py probeEnergy broadening) =
      pauliGreenOperator side v m px py probeEnergy broadening := by
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix side v m px py probeEnergy broadening) = _
  simp [pauliGreenMatrix, pauliGreenOperator, matrixOperator, map_add, map_smul]

private def raPauliXScalarCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  ((Real.cos θ : ℝ) : ℂ) * (aA * bR + aR * bA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (bA * dR - bR * dA)

private def raPauliXXCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  aR * aA - dR * dA +
    bR * bA * ((((Real.cos θ : ℝ) : ℂ) ^ 2) - (((Real.sin θ : ℝ) : ℂ) ^ 2))

private def raPauliXYCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  Complex.I * (aA * dR - aR * dA) +
    2 * bR * bA * ((Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℝ) : ℂ)

private def raPauliXZCoefficient
    (v m p θ probeEnergy broadening : ℝ) : ℂ :=
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  ((Real.cos θ : ℝ) : ℂ) * (bA * dR + bR * dA) +
    Complex.I * ((Real.sin θ : ℝ) : ℂ) * (aR * bA - aA * bR)

/-- Exact pointwise Pauli decomposition of the repository-oriented `Gᴿ σₓ Gᴬ` rung in polar
coordinates. -/
theorem retardedAdvancedPauliX_polar_eq
    (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenMatrix .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * sigmaX *
      pauliGreenMatrix .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      raPauliXScalarCoefficient v m p θ probeEnergy broadening • (1 : Matrix2) +
        raPauliXXCoefficient v m p θ probeEnergy broadening • sigmaX +
        raPauliXYCoefficient v m p θ probeEnergy broadening • sigmaY +
        raPauliXZCoefficient v m p θ probeEnergy broadening • sigmaZ := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliGreenMatrix, raPauliXScalarCoefficient, raPauliXXCoefficient,
      raPauliXYCoefficient, raPauliXZCoefficient, Matrix.mul_apply,
      pauliGreenScalarCoefficient_polar, pauliGreenXCoefficient_polar,
      pauliGreenYCoefficient_polar, pauliGreenZCoefficient_polar,
      sigmaX, sigmaY, sigmaZ] <;>
    ring_nf <;>
    simp [hI]

/-- Operator form of the exact pointwise Pauli decomposition, obtained by transporting the matrix
identity through the canonical matrix/operator equivalence. -/
theorem retardedAdvancedPauliXOperator_polar_eq
    (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * matrixOperator sigmaX *
      pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      raPauliXScalarCoefficient v m p θ probeEnergy broadening •
          (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        raPauliXXCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaX +
        raPauliXYCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaY +
        raPauliXZCoefficient v m p θ probeEnergy broadening • matrixOperator sigmaZ := by
  rw [← matrixOperator_pauliGreenMatrix, ← matrixOperator_pauliGreenMatrix]
  change
    (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix .retarded v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)) sigmaX *
      (Matrix.toEuclideanCLM : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert))
        (pauliGreenMatrix .advanced v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening) = _
  rw [← map_mul, ← map_mul, retardedAdvancedPauliX_polar_eq]
  simp [matrixOperator, map_add, map_smul]

/-- Radial `σₓ` coefficient after the full polar-angle average of `Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularXCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) *
    (pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening -
      pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Radial orientation-sensitive `σᵧ` coefficient after the full polar-angle average of
`Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularYCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)) * Complex.I *
    (pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening -
      pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening *
        pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Full polar-angle operator rung at fixed radial momentum. -/
noncomputable def continuumAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * matrixOperator sigmaX *
      pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening

end

end AnomalousHall.MassiveDirac
