import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.ResolventSpectral
import LeanCondensedMatter.Transport.ResolventEnergyDerivative

set_option linter.style.header false

/-!
# Transport resolvent API

Public umbrella for the generic retarded/advanced resolvent layer: dimension-independent resolvent
identities, finite pure-point spectral action, and energy-derivative identities.

No conductivity, occupation integral, Středa decomposition, disorder approximation, or concrete
model specialization is introduced here.
-/
