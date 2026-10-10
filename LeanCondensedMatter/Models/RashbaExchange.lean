import LeanCondensedMatter.Models.RashbaExchange.Model
import LeanCondensedMatter.Models.RashbaExchange.Model.Spectral
import LeanCondensedMatter.Models.RashbaExchange.Model.Interband
import LeanCondensedMatter.Models.RashbaExchange.Model.OperatorSpectral
import LeanCondensedMatter.Models.RashbaExchange.Operator
import LeanCondensedMatter.Models.RashbaExchange.Green
import LeanCondensedMatter.Models.RashbaExchange.Response
import LeanCondensedMatter.Models.RashbaExchange.Bastin.Berry

set_option linter.style.header false

/-!
# Finite Rashba-exchange anomalous-Hall benchmark

Public route for the finite-cutoff, finite-broadening two-band Rashba-exchange model, its spectral
projectors, and the interband current-block/Berry-curvature bridge. Fixed-window clean-limit pole
extraction remains downstream.
-/
