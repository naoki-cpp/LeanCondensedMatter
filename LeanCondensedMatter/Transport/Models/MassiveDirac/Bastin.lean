import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Berry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Bands
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Limit
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleFactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleWindow
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleContinuity
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleWindowBound
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleExtraction
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PairIntegral
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PairBerry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.CleanLimit
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialDomination
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialSpectatorBound
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialSpectatorUniformBound
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialPairUniformBound
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialDominatedConvergence
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.RadialEnergyBridge
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.ZeroTemperaturePair

set_option linter.style.header false

/-!
# Massive-Dirac Bastin analysis

Public umbrella for the concrete massive-Dirac finite/zero-broadening Bastin proof chain. Canonical
implementations live under `MassiveDirac/Bastin/`; reusable analysis is extracted upstream instead
of being re-owned here.
-/
