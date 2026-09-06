import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Normalization
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinal

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson longitudinal Středa conductivity

This module is the conductivity-level consumer of the finite-cutoff finite-`η` longitudinal Středa
response owned upstream by `MassiveDirac.Streda.FiniteBroadeningBornLadderLongitudinal`. It attaches
the common static Bastin/Středa conductivity prefactor and physical two-dimensional momentum-measure
normalization exactly once.

The shared nonzero determinant required for the in-plane ladder fixed point remains an explicit
hypothesis. No disorder, broadening, ultraviolet, thermodynamic, or simultaneous limit is taken here,
and the Born-Dyson candidate is not identified with an exact disorder average.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Physically normalized finite-cutoff finite-`η` longitudinal Středa surface conductivity bridge.
The explicit angle integral already supplies the angular measure, so the physical momentum measure
is attached without an extra `2π` factor. The nonzero ladder determinant is an explicit input, so
this object is only exposed where the solved two-component vertex is known to represent the ladder
fixed point. This is the finite-`η` conductivity-level insertion needed before any separately
justified weak-disorder or zero-broadening recovery of the RTA benchmark. -/
noncomputable def finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge
    (e v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar pMax) : ℂ :=
  ((bastinTraceConductivityPrefactor hbar * momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral
      e v m probeEnergy broadening disorderStrength hbar pMax hdet

/-- With zero radial cutoff, the physically normalized longitudinal surface conductivity bridge
vanishes exactly whenever the in-plane ladder is regular. -/
@[simp]
theorem finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge_zero_cutoff
    (e v m probeEnergy broadening disorderStrength hbar : ℝ)
    (hdet : finiteCutoffContinuumBornDysonLadderRegular
      v m probeEnergy broadening disorderStrength hbar 0) :
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge
      e v m probeEnergy broadening disorderStrength hbar 0 hdet = 0 := by
  simp [finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceConductivityBridge,
    finiteCutoffContinuumBornDysonLongitudinalRetardedAdvancedDressedSurfaceMomentumIntegral]

end

end QuantumTheory.Transport.Models.MassiveDirac
