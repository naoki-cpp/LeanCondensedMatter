import LeanCondensedMatter.Transport.Core
import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Public entry point for the main transport infrastructure. `Transport.Core` contains only the
shared dimension-independent transport primitives, while `Transport.FiniteConductivityTable` owns
the finite electrical-conductivity adapter built from generic Lehmann response data. The remaining
stable root groupings are `Transport.Resolvent`, `Transport.KuboBastin`, `Transport.Streda`, and
`Transport.Disorder`.

Model-independent analytical utilities are exposed through the separate opt-in package
`LeanCondensedMatter.Transport.Analysis`, covering occupation, angular harmonics, polar Fourier
reduction, and relaxation-time data. This root module intentionally does not import that package, so
consumers of the main transport interfaces do not acquire unrelated analysis utilities transitively.

Concrete model benchmarks are exposed separately through `LeanCondensedMatter.Transport.Models`; the
generic transport umbrella intentionally does not import them.
-/
