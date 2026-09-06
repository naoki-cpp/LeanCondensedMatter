import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderIntegral

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson Hall conductivity component

This module is the downstream physical-normalization consumer of the finite-cutoff finite-`η`
Hall Středa momentum response. The upstream Středa layer owns the pointwise surface trace, full
polar-angle integral, radial Jacobian, and finite-cutoff momentum integral.

This layer attaches `bastinTraceConductivityPrefactor hbar` and
`momentumMeasurePrefactor hbar` exactly once and exposes the physically normalized ordered
`x`-measured/`y`-source conductivity-component bridge. It is not identified with the antisymmetric
Hall projection until a downstream theorem relates the ordered `xy` and `yx` components. It is also
not yet the final non-crossing conductivity theorem or an exact disorder average. No broadening,
disorder, or ultraviolet limit is taken here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physically normalized finite-cutoff finite-`η` ordered `xy` conductivity-component bridge. The
upstream angle integral already supplies the angular measure, so `momentumMeasurePrefactor hbar` is
attached without an additional `2π` factor. This is not yet the antisymmetric Hall projection
`(σxy - σyx) / 2`. -/
noncomputable def finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceXYConductivityComponentBridge
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceMomentumIntegral
      e v m probeEnergy broadening disorderStrength hbar pMax

/-- With zero radial cutoff, the physically normalized ordered `xy` conductivity-component bridge
vanishes exactly. -/
@[simp]
theorem finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceXYConductivityComponentBridge_zero_cutoff
    (e v m probeEnergy broadening disorderStrength hbar : ℝ) :
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceXYConductivityComponentBridge
      e v m probeEnergy broadening disorderStrength hbar 0 = 0 := by
  simp [finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceXYConductivityComponentBridge,
    finiteCutoffContinuumBornDysonHallRetardedAdvancedDressedSurfaceMomentumIntegral]

end

end QuantumTheory.Transport.Models.MassiveDirac
