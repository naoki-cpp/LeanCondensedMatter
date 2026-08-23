import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleWindowBound
import LeanCondensedMatter.Transport.Analysis.LorentzianPole

set_option linter.style.header false

/-!
# Massive-Dirac specialization of the generic Lorentzian pole integral

The analytic error decomposition and zero-broadening extraction are owned generically by
`Transport.Analysis.LorentzianPole`.  This module now owns only the massive-Dirac specialization of
the fixed-window Lorentzian integral.  The limit theorem is stated in `PoleExtractionLimit`.

No model-local error split or duplicate approximate-identity proof remains here.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Lorentzian-weighted target-centered integral of the regular interband spectator/current factor.
This is the massive-Dirac specialization of `lorentzianRegularFactorIntegral`. -/
noncomputable def targetCenteredInterbandSpectatorCurrentPoleIntegral
    (band : Band) (e v m px py radius broadening : ℝ) : ℂ :=
  lorentzianRegularFactorIntegral
    (targetCenteredInterbandSpectatorCurrentFactor band e v m px py)
    radius broadening

end

end AnomalousHall.MassiveDirac
