import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Berry
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Bands
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Interband
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Limit
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.Spectator
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleFactor
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleWindow
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleContinuity
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PoleExtraction
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PairIntegral
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.PairBerry
import LeanCondensedMatter.Transport.Models.RashbaExchange.Bastin.CleanLimit

set_option linter.style.header false

/-!
# Rashba-exchange Bastin clean-limit bridge

Public entry point for the finite-band projector decomposition and fixed-window pointwise
zero-broadening bridge from the Rashba-exchange Bastin Hall pair to its clean Berry-curvature
density. Momentum integration and limit interchange remain outside this module.
-/
