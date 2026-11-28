import LeanCondensedMatter.QuantumTheory.ScatteringRate
import LeanCondensedMatter.QuantumTheory.LocalizedSpin
import LeanCondensedMatter.QuantumTheory.PlanckConstant
import LeanCondensedMatter.QuantumTheory.Postulates
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumTheory.SpinHalf.Finite
import LeanCondensedMatter.QuantumTheory.SpinfulLattice
import LeanCondensedMatter.QuantumTheory.PeierlsPhase
import LeanCondensedMatter.QuantumTheory.PeierlsLattice
import LeanCondensedMatter.QuantumTheory.ConservationLaw
import LeanCondensedMatter.QuantumTheory.Occupation
import LeanCondensedMatter.QuantumTheory.TwoBand
import LeanCondensedMatter.QuantumTheory.LinearResponse
import LeanCondensedMatter.QuantumTheory.DensityOperator
import LeanCondensedMatter.QuantumTheory.POVM
import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Basic
import LeanCondensedMatter.QuantumTheory.Entropy.Diagonal
import LeanCondensedMatter.QuantumTheory.Entropy.Finite
import LeanCondensedMatter.QuantumTheory.Gibbs

set_option linter.style.header false

/-!
# Quantum theory

Particle-statistics-independent quantum theory: postulates, quantum states, measurements,
entropy, Gibbs states, spectral occupations, spins and two-band spectra, Peierls lattice
coupling, conservation laws, scattering rates, and linear response.
-/
