import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.FiniteBroadeningBornLadder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinalZeroBroadeningIntegral

set_option linter.style.header false

/-!
# Zero-broadening longitudinal Born-Dyson Středa conductivity

This module attaches the physical Bastin/Středa conductivity prefactor and continuum momentum
normalization to the fixed-cutoff ordered `xx` Středa momentum-integral zero-broadening boundary.
The response analysis and radial integration remain owned upstream by `MassiveDirac.Streda`.

The disorder strength and cutoff remain fixed. No weak-disorder, ultraviolet, thermodynamic, or
simultaneous limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open Filter QuantumTheory.Transport

/-- Physically normalized fixed-cutoff zero-broadening boundary of the longitudinal ordered `xx`
Born-Dyson Středa surface conductivity. -/
def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
    (e v m probeEnergy disorderStrength hbar pMax : ℝ) : ℂ :=
  ((bastinStredaConductivityNormalization hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegralZeroBroadeningBoundary
      e v m probeEnergy disorderStrength hbar pMax

/-- At fixed positive disorder and finite cutoff, the physically normalized longitudinal ordered
`xx` component of the Born-Dyson Středa conductivity tensor converges to its zero-broadening
boundary. -/
theorem tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivity_broadening_zero
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
        (finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor
          e v m probeEnergy broadening disorderStrength hbar pMax).component .x .x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary
          e v m probeEnergy disorderStrength hbar pMax)) := by
  have h :=
    tendsto_finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral_broadening_zero
      e v m probeEnergy disorderStrength hbar pMax hpMax hvelocity hhbar
      hdisorder hmetal hcutoff hrenorm hdet
  simpa [
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceConductivityTensor,
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityZeroBroadeningBoundary] using
    h.const_mul (((bastinStredaConductivityNormalization hbar : ℝ) : ℂ))

end

end QuantumTheory.Transport.Models.MassiveDirac
