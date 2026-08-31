import LeanCondensedMatter.Transport.Core
import LeanCondensedMatter.Transport.Resolvent
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Public entry point for generic transport infrastructure. Canonical implementations are physically
grouped under `Transport/Core/`, `Transport/Resolvent/`, `Transport/KuboBastin/`,
`Transport/Streda/`, `Transport/Disorder/`, and `Transport/Analysis/`.

The stable public groupings are `Transport.Core`, `Transport.Resolvent`, `Transport.KuboBastin`,
`Transport.Streda`, and `Transport.Disorder`. Concrete model benchmarks are exposed separately through
`LeanCondensedMatter.Transport.Models`; the generic transport umbrella intentionally does not import
them.
-/
