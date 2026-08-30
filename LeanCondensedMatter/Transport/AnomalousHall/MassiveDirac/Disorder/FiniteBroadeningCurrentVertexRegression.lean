import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.CurrentVertexAngular
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder.FiniteBroadeningCurrentVertexAngular

set_option linter.style.header false

/-!
# Finite-broadening Born-Dyson current-rung regressions

Regression bridges for the finite-external-broadening Born-Dyson angular rung.  These statements
keep the disorder-dependent derivation tied to the existing clean finite-broadening result without
adding a second physical approximation.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

/-- At zero disorder strength, the finite-`η` Born-Dyson `σₓ` rung reduces exactly to the existing
clean finite-broadening angular rung. -/
@[simp] theorem finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral_zero_disorder
    (v m p probeEnergy broadening hbar pMax : ℝ) :
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening 0 hbar pMax =
      continuumAngularRetardedAdvancedPauliXIntegral
        v m p probeEnergy broadening := by
  simp [finiteCutoffContinuumBornDysonAngularRetardedAdvancedPauliXIntegral,
    finiteCutoffContinuumBornDysonAngularRetardedAdvancedInPlaneRungAction,
    continuumAngularRetardedAdvancedPauliXIntegral]

end

end AnomalousHall.MassiveDirac
