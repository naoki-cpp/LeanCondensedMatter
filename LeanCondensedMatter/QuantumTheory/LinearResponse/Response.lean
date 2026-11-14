import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.KuboFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.SourceCoupling
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.RetardedSusceptibility
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.DensitySusceptibility
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.ObservableVariation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel

set_option linter.style.header false

/-!
# Public response-formula package

Focused entry point for the bounded Kubo formula, source-coupled and retarded
susceptibilities, density response, observable variation, and channel response.
The declaration owners are the individual `Response/*` modules.

For the complete bounded response framework (including dynamics, frequency
transforms, and Lehmann representations), import `QuantumTheory.LinearResponse`.
-/
