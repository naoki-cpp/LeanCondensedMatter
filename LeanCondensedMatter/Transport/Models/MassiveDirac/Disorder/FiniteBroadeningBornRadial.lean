import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson radial propagator data

This module owns radial propagator-level combinations that are reused by current-vertex and
zero-broadening consumers.  No vertex algebra or limiting procedure is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

/-- Product of the radial retarded and advanced finite-`η` Born-Dyson denominators. -/
def finiteCutoffContinuumBornDysonRetardedAdvancedDenominatorProduct
    (v m p probeEnergy broadening disorderStrength hbar pMax : ℝ) : ℂ :=
  finiteCutoffContinuumBornDysonDenominator
      .retarded v m p 0 probeEnergy broadening disorderStrength hbar pMax *
    finiteCutoffContinuumBornDysonDenominator
      .advanced v m p 0 probeEnergy broadening disorderStrength hbar pMax

end

end QuantumTheory.Transport.Models.MassiveDirac
