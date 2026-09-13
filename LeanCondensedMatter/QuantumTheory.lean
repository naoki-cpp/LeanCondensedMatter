import LeanCondensedMatter.QuantumTheory.Postulates
import LeanCondensedMatter.QuantumTheory.ConservationLaw
import LeanCondensedMatter.QuantumTheory.LinearResponse
import LeanCondensedMatter.QuantumTheory.DensityOperator
import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Finite
import LeanCondensedMatter.QuantumTheory.Gibbs

set_option linter.style.header false

/-!
# Quantum theory

Public entry point for particle-number-independent quantum theory: postulates, density operators,
entropy and Gibbs-state theory, one-body conservation/current semantics, together with the generic
linear-response stack.

The linear-response and Gibbs hierarchies are exposed through package-level routing modules. Existing
semantic bases such as `ConservationLaw`, `DensityOperator`, and `Entropy` remain unchanged.

Concrete first-quantized realizations belong to `QuantumMechanics`, while second-quantized model
specializations belong to `SecondQuantization`. Implementation modules should import narrow leaves
rather than this umbrella.
-/
