import LeanCondensedMatter.Transport.Core.FiniteVolume
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.FiniteConductivityTable

set_option linter.style.header false

/-!
# Transport core

Public entry point for representation-independent finite transport data: positive physical volume,
conductivity normalization, and finite scalar conductivity tables. General finite-dimensional
operator trace infrastructure is owned upstream by `Analysis.Operator.FiniteTrace`.
-/
