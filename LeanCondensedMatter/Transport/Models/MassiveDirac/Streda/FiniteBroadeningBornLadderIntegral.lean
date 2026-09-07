import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Středa surface momentum response

This module integrates the finite-cutoff finite-`η` RA-dressed/bare-same-side Středa surface trace
bridge over the two-dimensional momentum domain in polar coordinates. The measured current remains
fixed to `jₓ`, while the source direction is carried explicitly by `Direction2` from the pointwise
response through the angular integral, radial Jacobian, and finite-cutoff momentum integral.

No Bastin/Středa conductivity prefactor, physical momentum-measure prefactor, Hall
antisymmetrization, disorder/broadening limit, ultraviolet removal, mechanism label, or exact
disorder-average claim is introduced here. Physical conductivity normalization remains downstream
under `MassiveDirac.Conductivity`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

/-- Full polar-angle integral of the finite-`η` RA-dressed Středa surface trace bridge at fixed
radial momentum for the requested source direction. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
    (source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
      source e v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy broadening disorderStrength hbar pMax hdet

/-- Radial integrand for the finite-`η` source-indexed Středa surface response after the full
polar-angle integral, including exactly one polar Jacobian factor `p`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
    (source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
      source e v m p probeEnergy broadening disorderStrength hbar pMax hdet

/-- Finite-cutoff polar momentum integral of the finite-`η` source-indexed Středa surface response
before the Bastin/Středa trace prefactor and physical momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
    (source : Direction2)
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
      source e v m p probeEnergy broadening disorderStrength hbar pMax hdet

end

end QuantumTheory.Transport.Models.MassiveDirac
