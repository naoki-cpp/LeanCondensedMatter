import LeanCondensedMatter.Models.MassiveDirac.Disorder.Propagator.BornDyson.RealSpace.FrozenCutoffUV
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.BesselJ

set_option linter.style.header false

/-!
# Born-Dyson frozen-cutoff UV value in the Bessel-J representation

Connects the physical Born-Dyson Green-function cutoff to the general massive-Dirac
fixed-center Bessel-J Fourier UV value.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open MeasureTheory
open scoped Interval ComplexConjugate

/-- The finite-Born reference-cutoff radial Green UV value has the same
Bessel-J spectral center and one physical momentum-measure prefactor. -/
theorem finiteCutoffContinuumBornDysonRadialFrozenUVValue_eq_besselJCenter
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pRef radius : ℝ) :
    finiteCutoffContinuumBornDysonRadialFrozenUVValue
      side v m probeEnergy broadening disorderStrength hbar pRef radius =
      (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
        massiveDiracRadialBesselJCenterUVValue v (radius / hbar)
          ((finiteCutoffContinuumBornEffectiveEnergy
              side v m probeEnergy broadening disorderStrength hbar pRef) ^ 2 -
           (finiteCutoffContinuumBornEffectiveMass
              side v m probeEnergy broadening disorderStrength hbar pRef) ^ 2) := by
  unfold finiteCutoffContinuumBornDysonRadialFrozenUVValue
  dsimp only
  rw [massiveDiracRadialFourierUVCenter_eq_besselJCenter]

end

end QuantumTheory.Models.MassiveDirac
