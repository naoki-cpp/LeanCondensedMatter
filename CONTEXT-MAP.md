# Context map

This repository formalizes condensed-matter physics in Lean. Here, a context means a cohesive domain vocabulary and boundary, not necessarily a Lean namespace or package. This map identifies each context's scope and existing language sources; it is a navigation aid, not an import/dependency specification. Use Lean declarations as the authority for mathematical meaning and architecture notes for current ownership and dependencies.

## Contexts

### Mathematical foundations and combinatorics

Reusable operator analysis, finite combinatorics, permutations, orderings, pairings, and connected decompositions belong here. Their mathematical meaning is stated in Lean and Mathlib declarations; project-level boundaries are summarized in [the conventions](docs/conventions.md), [order-decomposition architecture](docs/architecture/combinatorics-order-decomposition.md), [ADR 0001](docs/adr/0001-lean-and-mathlib.md), and [ADR 0002](docs/adr/0002-semantic-ownership.md). Physical assumptions do not belong in this context. The [finite-combinatorics glossary](docs/glossary/combinatorics/CONTEXT.md) defines ambient slot shuffles independently of their recursive presentation.

### Quantum theory

This context owns state, observable, measurement, equilibrium, entropy, and general response-channel concepts. Use the [quantum density-state architecture](docs/architecture/quantum-density-theory.md), [models and assumptions](docs/model-and-assumptions.md), [ADR 0003](docs/adr/0003-density-backed-states.md), [ADR 0004](docs/adr/0004-physical-scalar-types.md), [ADR 0015](docs/adr/0015-countable-discrete-povms.md), and [ADR 0016](docs/adr/0016-heat-operator-first-gibbs-states.md) for current definitions and boundaries.

### Second quantization

This context covers occupation data and Fock representations, field operators, thermal expectations, diagrammatics, and linked-cluster results. The [second-quantization terminology reference](docs/glossary/second-quantization-terminology.md) records preferred wording alongside implementation pointers; the [architecture note](docs/architecture/second-quantization.md) records ownership and dependency direction. The enduring boundaries are recorded in [ADR 0005](docs/adr/0005-fock-representations.md), [ADR 0006](docs/adr/0006-thermal-expectation-recursion.md), [ADR 0007](docs/adr/0007-bosonic-summability-domains.md), and [ADR 0008](docs/adr/0008-diagrammatics-and-analysis.md).

### Transport

This context covers generic resolvent and response representations, disorder methods, and the boundary where physical conductivity is normalized. The [transport architecture](docs/architecture/transport.md), [models and assumptions](docs/model-and-assumptions.md), and [ADR 0009](docs/adr/0009-response-and-conductivity.md) define the current scope.

The root [CONTEXT.md](CONTEXT.md) is a narrower subcontext: it defines terms for finite-cutoff MassiveDirac transport and its current-response construction. Its terms do not define generic transport vocabulary for the whole repository.

### Crystal structure

This context derives periodic structure, reciprocal-lattice conventions, and the Brillouin quotient from atomic configurations. See [ADR 0017](docs/adr/0017-crystal-from-atomic-configurations.md) and the Crystal declarations linked there.

### Spectral and Berry geometry

The generic finite-band layer provides pointwise spectral and Berry geometry. Global lattice topology and physical response belong to downstream model consumers with their own assumptions; pointwise identities alone establish neither. See [ADR 0018](docs/adr/0018-finite-band-berry-geometry.md) and its linked declarations.

## Relationships

- `Analysis`, `Combinatorics`, and `Permutation` provide reusable mathematics to the physics contexts; physical assumptions remain downstream.
- `QuantumTheory` owns general state and response-channel concepts. `SecondQuantization` supplies many-body representations and thermal constructions; `Transport` supplies transport-specific response representations and physical normalization.
- Within `SecondQuantization`, `Common` owns statistics-independent structures; `Fermionic` and `Bosonic` own their statistics-specific realizations.
- `Crystal` and pointwise Berry geometry supply distinct structures to periodic-band consumers. Their use by a physical model does not merge lattice structure, pointwise spectral geometry, and global topology into one context.

## Using the map

Architecture notes describe current module ownership, model notes state physical assumptions, and ADRs explain enduring boundaries and trade-offs. They are complementary sources rather than interchangeable glossaries. Add or refine a context glossary when a project-specific term needs a stable definition; keep implementation details in architecture notes and code.
