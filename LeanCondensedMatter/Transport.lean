import LeanCondensedMatter.Transport.Core
import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Model-independent transport theory: dimension-independent conductivity data, finite Lehmann
conductivity evaluation, retarded/advanced resolvents, Kubo–Bastin response, Středa response, and
finite-disorder transport.

Analytical utilities such as occupation functions, angular harmonics, polar reduction, and
relaxation-time data live in `Transport.Analysis`. Concrete Hamiltonian benchmarks live in
`Transport.Models`.
-/
