import LeanCondensedMatter.Transport.Resolvent.Basic
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import LeanCondensedMatter.Transport.Analysis.LorentzianKernel

set_option linter.style.header false

/-!
# Transport resolvent API

Transitional public umbrella for the physical `Transport.Resolvent/` hierarchy and the reusable
Lorentzian pole kernel. The final public entry is being migrated to `Transport.Resolvent` once all
internal imports no longer use the historical basic-resolvent path.
-/
