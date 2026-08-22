import LeanCondensedMatter.Transport.Core
import LeanCondensedMatter.Transport.ResolventAPI
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Public entry point for generic transport infrastructure. Canonical implementations are physically
grouped under `Transport/Core/`, `Transport/Resolvent/`, `Transport/KuboBastin/`,
`Transport/Streda/`, `Transport/Disorder/`, and `Transport/Analysis/`.

Concrete model umbrellas such as `LeanCondensedMatter.Transport.AnomalousHall` remain explicit
downstream imports rather than part of this generic umbrella.
-/
