import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.BornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator

set_option linter.style.header false

/-!
# Bounded-operator realization of the Born-dressed propagator

The Born propagator coefficients are defined in `BornPropagator.lean`.  This file gives those
coefficients one canonical `2 × 2` matrix and bounded-operator realization for downstream response
kernels.

These are model-specific Born approximation objects.  They are not asserted to be exact
disorder-averaged Green operators or exact resolvents of the clean Hamiltonian.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- Canonical matrix assembled from the Born-dressed Pauli coefficients. -/
def continuumBornGreenMatrix
    (side : QuantumTheory.Transport.SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) : Matrix2 :=
  continuumBornPauliGreenScalarCoefficient
      side v m px py probeEnergy disorderStrength hbar • (1 : Matrix2) +
    continuumBornPauliGreenXCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaX +
    continuumBornPauliGreenYCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaY +
    continuumBornPauliGreenZCoefficient
      side v m px py probeEnergy disorderStrength hbar • sigmaZ

/-- Canonical bounded-operator realization of the Born-dressed Pauli propagator. -/
noncomputable def continuumBornGreenOperator
    (side : QuantumTheory.Transport.SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator
    (continuumBornGreenMatrix
      side v m px py probeEnergy disorderStrength hbar)

@[simp] theorem matrixOperator_continuumBornGreenMatrix
    (side : QuantumTheory.Transport.SpectralSide)
    (v m px py probeEnergy disorderStrength hbar : ℝ) :
    matrixOperator
        (continuumBornGreenMatrix
          side v m px py probeEnergy disorderStrength hbar) =
      continuumBornGreenOperator
        side v m px py probeEnergy disorderStrength hbar :=
  rfl

end

end AnomalousHall.MassiveDirac
