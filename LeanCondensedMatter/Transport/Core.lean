import LeanCondensedMatter.Transport.Core.FiniteVolume
import LeanCondensedMatter.Transport.Core.ConductivityNormalization
import LeanCondensedMatter.Transport.Core.ConductivityTensor

set_option linter.style.header false

/-!
# Transport core

Public entry point for dimension-independent transport data: positive physical volume, conductivity
normalization, and conductivity tensors. Finite electrical-conductivity table evaluation is a
downstream adapter owned by `Transport.FiniteConductivityTable`. General finite-dimensional operator
trace infrastructure is owned upstream by `Analysis.Operator.FiniteTrace`.
-/
