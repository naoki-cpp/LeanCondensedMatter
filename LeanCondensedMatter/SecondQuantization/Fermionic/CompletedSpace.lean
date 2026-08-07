import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnboundedExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbsSummability
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteOperatorCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteThermalCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation

set_option linter.style.header false

/-!
# Completed fermionic Fock-space analysis

The public entry point for the completed fermionic representation. The current slice contains the
`ℓ²` occupation representation, the dense algebraic core, the bounded single-mode number
projection, the occupation-toggle equivalence, bounded creation and annihilation maps, their
occupation-basis action, agreement with the algebraic ladder operators on the finite-support core,
and the canonical anticommutation relations lifted to the completion by density and continuity.
It also exposes domain-carrying diagonal partial operators, including the completed free Hamiltonian
and total-number operator on their natural weighted `ℓ²` domains. Maximal diagonal multiplication
operators are densely defined and closed, their adjoints are the conjugate-weight diagonal
operators, and conjugation-fixed weights are self-adjoint; in particular this applies to the free
Hamiltonian and total-number operator.

Under explicit absolute summability of the occupation Boltzmann weights, the completed free Gibbs
state is a genuine trace-class `DensityOperator`. Bounded expectations use the canonical
density-state API, while integrable unbounded diagonal observables are represented separately by
absolutely convergent occupation-basis series. In particular this gives explicit expectation
interfaces for the completed free Hamiltonian and total particle number without coercing either
unbounded operator into `ContinuousLinearMap`.

For the free fermion state, summability of the one-particle Boltzmann factors
`exp (-β εᵢ)` is a concrete sufficient condition for occupation-level Gibbs summability. Under this
condition the partition function satisfies the infinite product formula
`Z(β) = ∏' i, (1 + exp (-β εᵢ))`.

When the mode type is finite, the completed `ℓ²` representation is canonically linearly isometric to
the existing `Common.FiniteHilbertFock` occupation realization, with occupation coordinates, basis
vectors, and the algebraic-core embedding identified explicitly. Any bounded completed operator
that agrees with an algebraic Fock endomorphism on the canonical core transports to the existing
`Common.finiteHilbertOperator`; this identifies the completed number, creation, and annihilation
operators with their finite-Hilbert realizations. In finite mode dimension Gibbs summability is
automatic, the completed and finite partition functions and normalized weights coincide, and the
completed free Gibbs density operator intertwines with the existing finite Gibbs state under the
same isometry.

For arbitrary mode types, finite-mode coordinate projections indexed by `Finset Mode` form a
contractive net converging strongly to the identity. This provides the first explicit C5
approximation theorem without imposing a countability assumption on the mode set.

Thermodynamic-limit constructions remain later work.
-/
