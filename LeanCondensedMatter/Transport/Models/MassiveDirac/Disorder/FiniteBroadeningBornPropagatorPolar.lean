import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Vertex.PauliRung
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Polar form of the finite-broadening Born-Dyson propagator

Shared bridge from the Cartesian finite-cutoff finite-`η` Born-Dyson Green operator to the
massive-Dirac polar Pauli representation. This theorem belongs to the propagator representation
boundary rather than to a particular current-vertex or Středa consumer.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- The Cartesian finite-`η` Born-Dyson propagator reduces exactly to the shared polar Pauli form. -/
theorem finiteCutoffContinuumBornDysonGreenOperator_polar_eq
    (side : SpectralSide)
    (v m p θ probeEnergy broadening disorderStrength hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonGreenOperator
        side v m (p * Real.cos θ) (p * Real.sin θ)
        probeEnergy broadening disorderStrength hbar pMax =
      polarPauliOperator
        (finiteCutoffContinuumBornDysonScalarCoefficient
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonPauliCoefficient .x
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
        (finiteCutoffContinuumBornDysonPauliCoefficient .z
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax) θ := by
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hradial :
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 = p ^ 2 + 0 ^ 2 := by
    calc
      (p * Real.cos θ) ^ 2 + (p * Real.sin θ) ^ 2 =
          p ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = p ^ 2 := by rw [htrig]; ring
      _ = p ^ 2 + 0 ^ 2 := by ring
  have hden :
      finiteCutoffContinuumBornDysonDenominator
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax =
        finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax := by
    unfold finiteCutoffContinuumBornDysonDenominator
    rw [hradial]
  simpa [finiteCutoffContinuumBornDysonGreenOperator,
    finiteCutoffContinuumBornDysonGreenMatrix,
    finiteCutoffContinuumBornDysonScalarCoefficient,
    finiteCutoffContinuumBornDysonPauliCoefficient, pauliAxisComponent, hden] using
    (commonDenominatorPauliOperator_polar_eq
      (finiteCutoffContinuumBornDysonDenominator
        side v m p 0 probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveEnergy
        side v m probeEnergy broadening disorderStrength hbar pMax)
      (finiteCutoffContinuumBornEffectiveMass
        side v m probeEnergy broadening disorderStrength hbar pMax)
      v p θ)

end

end QuantumTheory.Transport.Models.MassiveDirac
