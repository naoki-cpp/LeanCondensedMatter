import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Hall surface momentum integral

This module is the downstream physical-normalization consumer of the response-level finite-`η`
Hall Středa bridge in `Streda.FiniteBroadeningBornLadder`. The polar-angle integral remains explicit,
so the physical momentum measure contributes `momentumMeasurePrefactor hbar` exactly once together
with the polar Jacobian `p dp`.

The source vertex is the solved retarded-advanced ladder vertex while the explicit RR/AA same-side
remainder remains bare, exactly as upstream. Therefore the result is a physically normalized Hall
surface conductivity bridge, not yet the final non-crossing conductivity theorem and not an exact
disorder average. No broadening, disorder, or ultraviolet limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

/-- Full polar-angle integral of the finite-`η` RA-dressed Hall Středa surface trace bridge at fixed
radial momentum. -/
noncomputable def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceTraceBridge
      e v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy broadening disorderStrength hbar pMax

/-- Radial integrand for the finite-`η` RA-dressed Hall surface response after the full polar-angle
integral, including exactly one polar Jacobian factor `p`. -/
def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceAngularTraceIntegral
      e v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-cutoff polar momentum integral of the finite-`η` RA-dressed Hall surface response before
the Bastin/Středa trace prefactor and physical momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceMomentumIntegral
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceRadialIntegrand
      e v m p probeEnergy broadening disorderStrength hbar pMax

/-- Physically normalized finite-cutoff finite-`η` Hall surface conductivity bridge. The explicit
angle integral already supplies the angular measure, so `momentumMeasurePrefactor hbar` is attached
without an additional `2π` factor. -/
noncomputable def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceConductivityBridge
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ((bastinTraceHallPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceMomentumIntegral
      e v m probeEnergy broadening disorderStrength hbar pMax

/-- With zero radial cutoff, the physically normalized Hall surface bridge vanishes exactly. -/
@[simp]
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceConductivityBridge_zero_cutoff
    (e v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceConductivityBridge
      e v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceConductivityBridge,
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceMomentumIntegral]

end

end QuantumTheory.Transport.Models.MassiveDirac
