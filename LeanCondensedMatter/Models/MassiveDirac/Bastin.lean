import LeanCondensedMatter.Models.MassiveDirac.Bastin.Berry
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Bands
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Limit
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Spectator
import LeanCondensedMatter.Models.MassiveDirac.Bastin.Interband
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleFactor
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleWindow
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleContinuity
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PoleExtraction
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PairIntegral
import LeanCondensedMatter.Models.MassiveDirac.Bastin.PairBerry
import LeanCondensedMatter.Models.MassiveDirac.Bastin.CleanLimit
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialDomination
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialSpectatorBound
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialSpectatorUniformBound
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialPairUniformBound
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialDominatedConvergence
import LeanCondensedMatter.Models.MassiveDirac.Bastin.RadialEnergyBridge
import LeanCondensedMatter.Models.MassiveDirac.Bastin.ZeroTemperaturePair

set_option linter.style.header false

/-!
# Massive-Dirac Bastin analysis

Finite- and zero-broadening Bastin analysis for the massive-Dirac benchmark, including band and
Berry decompositions, pole extraction, clean limits, radial domination, dominated convergence, and
zero-temperature pair response.
-/
