import LeanCondensedMatter.Transport.Models.MassiveDirac.AngularReduction
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Angular reduction of the massive-Dirac retarded-advanced current rung

This Phase 5 entry point keeps the physical retarded-advanced ordering explicit while performing
only the clean-propagator specialization of the shared massive-Dirac polar Pauli rung algebra. At
fixed radial momentum it studies

```text
Gᴿ(p,θ) σₓ Gᴬ(p,θ)
```

before any radial integration, disorder normalization, zero-broadening limit, or ladder
resummation. The full polar-angle integral closes in the in-plane Pauli span. Reversing the
retarded/advanced order reverses the orientation-sensitive `σᵧ` term, so the order is not hidden by
a symmetric wrapper.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open MeasureTheory
open QuantumTheory.Transport
open scoped Interval

private theorem pauliGreenOperator_polar_eq
    (side : SpectralSide) (v m p θ probeEnergy broadening : ℝ) :
    pauliGreenOperator side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening =
      polarPauliOperator
        (pauliGreenScalarCoefficient side v m p 0 probeEnergy broadening)
        (pauliGreenXCoefficient side v m p 0 probeEnergy broadening)
        (pauliGreenZCoefficient side v m p 0 probeEnergy broadening) θ := by
  change
    pauliGreenScalarCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening • (1 : DiracHilbert →L[ℂ] DiracHilbert) +
        pauliGreenXCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening • matrixOperator sigmaX +
        pauliGreenYCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening • matrixOperator sigmaY +
        pauliGreenZCoefficient side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening • matrixOperator sigmaZ = _
  rw [pauliGreenScalarCoefficient_polar, pauliGreenXCoefficient_polar,
    pauliGreenYCoefficient_polar, pauliGreenZCoefficient_polar]
  unfold polarPauliOperator polarPauliMatrix matrixOperator
  simp only [map_add, map_smul, map_one]

/-- Radial `σₓ` coefficient after the full polar-angle average of `Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularXCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  pauliRungAngularXCoefficient
    (pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening)
    (pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening)
    (pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening)
    (pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Radial orientation-sensitive `σᵧ` coefficient after the full polar-angle average of
`Gᴿ σₓ Gᴬ`. -/
def retardedAdvancedPauliXAngularYCoefficient
    (v m p probeEnergy broadening : ℝ) : ℂ :=
  pauliRungAngularYCoefficient
    (pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening)
    (pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening)
    (pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening)
    (pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening)

/-- Full polar-angle operator rung at fixed radial momentum. -/
noncomputable def continuumAngularRetardedAdvancedPauliXIntegral
    (v m p probeEnergy broadening : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening * matrixOperator sigmaX *
      pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening

/-- The full retarded-advanced `x`-current rung closes exactly in the in-plane Pauli span. -/
theorem continuumAngularRetardedAdvancedPauliXIntegral_eq
    (v m p probeEnergy broadening : ℝ) :
    continuumAngularRetardedAdvancedPauliXIntegral v m p probeEnergy broadening =
      retardedAdvancedPauliXAngularXCoefficient v m p probeEnergy broadening •
          matrixOperator sigmaX +
        retardedAdvancedPauliXAngularYCoefficient v m p probeEnergy broadening •
          matrixOperator sigmaY := by
  let aR := pauliGreenScalarCoefficient .retarded v m p 0 probeEnergy broadening
  let aA := pauliGreenScalarCoefficient .advanced v m p 0 probeEnergy broadening
  let bR := pauliGreenXCoefficient .retarded v m p 0 probeEnergy broadening
  let bA := pauliGreenXCoefficient .advanced v m p 0 probeEnergy broadening
  let dR := pauliGreenZCoefficient .retarded v m p 0 probeEnergy broadening
  let dA := pauliGreenZCoefficient .advanced v m p 0 probeEnergy broadening
  unfold continuumAngularRetardedAdvancedPauliXIntegral
  rw [show
      (fun θ : ℝ =>
        pauliGreenOperator .retarded v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening * matrixOperator sigmaX *
          pauliGreenOperator .advanced v m (p * Real.cos θ) (p * Real.sin θ)
            probeEnergy broadening) =
        fun θ : ℝ =>
          polarPauliOperator aR bR dR θ *
            matrixOperator ((1 : ℂ) • sigmaX + (0 : ℂ) • sigmaY) *
            polarPauliOperator aA bA dA θ by
    funext θ
    rw [pauliGreenOperator_polar_eq, pauliGreenOperator_polar_eq]
    simp [aR, aA, bR, bA, dR, dA] ]
  simpa [retardedAdvancedPauliXAngularXCoefficient,
    retardedAdvancedPauliXAngularYCoefficient, aR, aA, dR, dA] using
    (integral_polarPauliOperator_inPlane_eq aR aA bR bA dR dA (1 : ℂ) 0)

end

end AnomalousHall.MassiveDirac
