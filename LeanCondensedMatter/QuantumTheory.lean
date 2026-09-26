import LeanCondensedMatter.QuantumTheory.Postulates
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumTheory.ConservationLaw
import LeanCondensedMatter.QuantumTheory.LinearResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics
import LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence
import LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion
import LeanCondensedMatter.QuantumTheory.LinearResponse.ConservationLaws
import LeanCondensedMatter.QuantumTheory.DensityOperator
import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Finite
import LeanCondensedMatter.QuantumTheory.Gibbs

set_option linter.style.header false

/-!
# Quantum theory

Particle-number-independent quantum theory: postulates, density operators and entropy, Gibbs states,
abstract conservation-law evolution, and generic linear response.

Concrete first-quantized realizations are developed in QuantumMechanics, while statistics-specific
many-body constructions are developed in SecondQuantization.
-/
