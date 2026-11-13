import LeanCondensedMatter.QuantumTheory.POVM.Basic
import LeanCondensedMatter.QuantumTheory.POVM.Born

set_option linter.style.header false

/-!
# Discrete POVM API

Public entry point for countable positive operator-valued measurements and their
Born-probability laws. Density operators are the upstream state model; the POVM
interface is a distinct measurement API. Use this import instead of the broader
`QuantumTheory.DensityOperator` umbrella when only POVMs are needed.
-/
