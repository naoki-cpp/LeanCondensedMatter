import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadder
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Středa surface momentum response

This module integrates the finite-cutoff finite-`η` RA-dressed/bare-same-side Středa surface trace
bridge over the two-dimensional momentum domain in polar coordinates. The measured-current and
source directions are carried explicitly by `Direction2` from the pointwise response through the
angular integral, radial Jacobian, and finite-cutoff momentum integral.

The values are algebraic candidates built from the total solved ladder coefficients; ladder
regularity is a separate condition for their fixed-point interpretation. No Bastin/Středa
conductivity prefactor, physical momentum-measure prefactor, Hall antisymmetrization,
disorder/broadening limit, ultraviolet removal, mechanism label, or exact disorder-average claim is
introduced here. Physical conductivity normalization remains downstream under
`MassiveDirac.Conductivity`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open MeasureTheory QuantumTheory.Transport
open scoped Interval

/-- Full polar-angle integral of the finite-`η` RA-dressed Středa surface trace bridge at fixed
radial momentum for the requested measured/source pair. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
    (measured source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceTraceBridge
      measured source e v m (p * Real.cos θ) (p * Real.sin θ)
      probeEnergy broadening disorderStrength hbar pMax

/-- Radial integrand for the finite-`η` pair-indexed Středa surface response after the full
polar-angle integral, including exactly one polar Jacobian factor `p`. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
    (measured source : Direction2)
    (e v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  (p : ℂ) *
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceAngularTraceIntegral
      measured source e v m p probeEnergy broadening disorderStrength hbar pMax

/-- Finite-cutoff polar momentum integral of the finite-`η` pair-indexed Středa surface response
before the Bastin/Středa trace prefactor and physical momentum-measure prefactor are attached. -/
noncomputable def finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceMomentumIntegral
    (measured source : Direction2)
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ∫ p in (0 : ℝ)..pMax,
    finiteCutoffContinuumBornDysonRetardedAdvancedDressedSurfaceRadialIntegrand
      measured source e v m p probeEnergy broadening disorderStrength hbar pMax

end

end QuantumTheory.Transport.Models.MassiveDirac
