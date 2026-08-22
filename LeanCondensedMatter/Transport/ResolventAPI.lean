import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.ResolventSpectral
import LeanCondensedMatter.Transport.ResolventEnergyDerivative
import LeanCondensedMatter.Transport.LorentzianSpectralKernel

set_option linter.style.header false

/-!
# Transport resolvent API

Public umbrella for the generic retarded/advanced resolvent layer: dimension-independent resolvent
identities, finite pure-point spectral action, energy-derivative identities, and the scalar
Lorentzian spectral kernel used by retarded-minus-advanced pole extraction.

No conductivity, occupation integral, Středa decomposition, disorder approximation, or concrete
model specialization is introduced here.
-/
