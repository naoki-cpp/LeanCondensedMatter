import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderHallZeroBroadeningIntegral

set_option linter.style.header false

/-!
# Zero-broadening ordered transverse Born-Dyson Středa conductivity

This module attaches the physical Bastin/Středa conductivity prefactor and continuum momentum
normalization to the fixed-cutoff source-`.y` Středa momentum-integral zero-broadening boundary.
The result remains the ordered `xy` conductivity component with measured current fixed along `x`;
identification with the antisymmetric Hall projection is downstream.

The disorder strength and cutoff remain fixed. No weak-disorder, ultraviolet, thermodynamic, or
simultaneous limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Physically normalized fixed-cutoff zero-broadening boundary of the ordered source-`.y`
Born-Dyson Středa surface conductivity component. -/
def finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
      e v m probeEnergy disorderStrength hbar pMax

/-- At fixed positive disorder and finite cutoff, the physically normalized ordered source-`.y`
Born-Dyson Středa surface conductivity converges to its zero-broadening boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivity_broadening_zero
    (e v m probeEnergy disorderStrength hbar pMax : ℝ)
    (hpMax : 0 ≤ pMax) (hvelocity : v ≠ 0) (hhbar : hbar ≠ 0)
    (hdisorder : 0 < disorderStrength) (hmetal : |m| < probeEnergy)
    (hcutoff : probeEnergy ^ 2 - m ^ 2 < v ^ 2 * pMax ^ 2)
    (hrenorm : finiteCutoffContinuumBornBoundaryRealRenormalization
      v m probeEnergy disorderStrength hbar pMax < 1)
    (hdet : finiteCutoffContinuumBornDysonLadderDeterminantZeroBroadeningBoundary
      v m probeEnergy disorderStrength hbar pMax ≠ 0) :
    Tendsto
      (fun broadening : ℝ =>
        finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityComponentBridge
          .y e v m probeEnergy broadening disorderStrength hbar pMax)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax)) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceMomentumIntegral_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  simpa [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityComponentBridge,
    finiteCutoffContinuumBornDysonOrderedXYRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary] using
    h.const_mul
      (((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ))

end

end QuantumTheory.Transport.Models.MassiveDirac
