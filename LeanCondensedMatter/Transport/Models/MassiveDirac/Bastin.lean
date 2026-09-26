import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Berry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Bands
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Limit
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleFactor
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleWindow
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin.PoleContinuity
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

Finite- and zero-broadening Bastin analysis for the massive-Dirac benchmark, including band and
Berry decompositions, pole extraction, clean limits, radial domination, dominated convergence, and
zero-temperature pair response.
-/
