import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Toggle
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Operators
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.DiagonalAnalytic
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ProductDomain
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeHamiltonianLadder
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.GibbsLadderIntertwining
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalLadder
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalPeel
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalPeelIndexed
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalKMS
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalFirstPair
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ThermalRecursion
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnboundedExpectation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FreeGibbsSummability
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteOperatorCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.FiniteThermalCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.ModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.GibbsModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.GibbsModeTruncationExpectation

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
Hamiltonian and total-number operator. The bounded fermionic ladder operators preserve the maximal
free-Hamiltonian domain, so the products `H a†`, `a† H`, `H a`, and `a H` are available as explicit
linear maps on `Dom(H)` rather than informal products of an unbounded operator. On that explicit
domain they satisfy the free-energy relations `[H, aᵢ†] = εᵢ aᵢ†` and
`[H, aᵢ] = -εᵢ aᵢ` as identities of linear maps.

Under explicit absolute summability of the occupation Boltzmann weights, the completed free Gibbs
state is a genuine trace-class `DensityOperator`. Bounded expectations use the canonical
density-state API, while integrable unbounded diagonal observables are represented separately by
absolutely convergent occupation-basis series. In particular this gives explicit expectation
interfaces for the completed free Hamiltonian and total particle number without coercing either
unbounded operator into `ContinuousLinearMap`. The Gibbs density operator also obeys the bounded
thermal-intertwining relations `ρβ aᵢ† = exp (-β εᵢ) aᵢ† ρβ` and
`ρβ aᵢ = exp (β εᵢ) aᵢ ρβ`. Creation and annihilation are additionally packaged as a single
completed thermal-ladder type carrying its Gibbs factor and scalar CAR coefficient. Repeated CAR
exchange is exposed as a bounded thermal peel identity. The canonical occupation-basis Gibbs
expectation also satisfies the completed KMS rotation `⟨C A⟩β = gβ(C) ⟨A C⟩β` for a thermal
ladder `C` and arbitrary bounded `A`, proved by reindexing the absolutely convergent Gibbs series by
the one-mode occupation toggle rather than introducing general trace cyclicity. Combining the peel
identity with this KMS rotation solves the wrapped term for odd tails with coefficient
`gβ(C) / (1 + gβ(C))`; the same coefficient gives the normalized completed two-point Gibbs value
from the scalar CAR coefficient. The recursive peel is also exposed in its position-indexed
`List.eraseIdx` form.

For the number-conserving normal-ordered free-fermion sector, same-type contractions vanish. The
concrete multipoint Gibbs expectation is therefore evaluated directly by a Mathlib determinant of
the creator–annihilator two-point matrix, multiplied by the fixed creator-first normal-order sign.
This determinant/Laplace representation is the concrete completed-space Bloch–de Dominicis endpoint;
it avoids perfect-pairing enumeration in the bipartite sector. General Gaussian fermionic
expectations with anomalous contractions are reserved for the later Pfaffian backend, while the
project `Pairing` type remains in use for genuine diagrammatic structure.

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
contractive net converging strongly to the identity. The same finite-mode net also restricts the
free Gibbs weights to occupations contained in each finite mode set. Under the existing absolute
Gibbs summability hypothesis these truncated partition functions converge to the full partition
function, every normalized occupation probability converges to its full Gibbs value, and the
normalized truncated Gibbs states converge weakly against every bounded operator.

Thermodynamic-limit constructions remain later work.
-/
