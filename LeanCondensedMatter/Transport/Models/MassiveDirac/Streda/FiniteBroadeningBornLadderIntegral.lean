import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Hall surface momentum response

This module integrates the finite-cutoff finite-`η` RA-dressed/bare-same-side Hall Středa surface
trace bridge over the two-dimensional momentum domain in polar coordinates. It owns only the
response-level angular integral, radial Jacobian, and finite-cutoff momentum integral.

No Bastin/Středa conductivity prefactor, physical momentum-measure prefactor, Hall
antisymmetrization, disorder/broadening limit, ultraviolet removal, mechanism label, or exact
disorder-average claim is introduced here. Physical conductivity normalization remains downstream
under `MassiveDirac.Conductivity`.
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

end

end QuantumTheory.Transport.Models.MassiveDirac
