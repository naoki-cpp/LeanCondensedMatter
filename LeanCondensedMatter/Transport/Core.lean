import LeanCondensedMatter.Transport.Core.FiniteVolume
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Core.FiniteConductivityTable

set_option linter.style.header false

/-!
# Transport core

Public entry point for representation-independent transport data: positive physical volume,
conductivity normalization, conductivity tensors, and finite scalar conductivity tables. General
finite-dimensional operator trace infrastructure is owned upstream by
`Analysis.Operator.FiniteTrace`.
-/
