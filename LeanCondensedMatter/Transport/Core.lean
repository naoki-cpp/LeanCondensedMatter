import LeanCondensedMatter.Transport.Core.FiniteVolume
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.FiniteConductivityTable
import LeanCondensedMatter.Transport.Core.FiniteTrace

set_option linter.style.header false

/-!
# Transport core

Public entry point for representation-independent finite transport data: positive physical volume,
conductivity normalization, finite scalar conductivity tables, and ordinary finite-dimensional
trace infrastructure.
-/
