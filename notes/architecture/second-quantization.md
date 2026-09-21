# Second-quantization architecture

This note records the stable ownership and dependency boundaries of
`LeanCondensedMatter/SecondQuantization/`. Lean declarations and the durable architecture audits under
`scripts/` are the source of truth; this document explains the intended shape of those checks.

## Ownership

Second-quantization declarations are owned by exactly one of three statistics layers:

```text
SecondQuantization.Common
SecondQuantization.Fermionic
SecondQuantization.Bosonic
```

Files under `SecondQuantization/Common/` own statistics-independent constructions that still depend
on second-quantized semantics: occupation/Fock infrastructure, imaginary-time and thermal interfaces,
finite operator integration, diagram data, component decompositions, shuffles, and other reusable
many-body constructions.

Files under `Fermionic/` and `Bosonic/` own statistics-specific algebra, signs, occupation rules,
Hamiltonians, convergence assumptions, physical specializations, and final physics-facing theorems.
A declaration should not remain in a statistics-specific layer merely because that is where its proof
was first developed.

Particle-statistics-independent one-body current semantics are not second-quantization declarations.
They live upstream under `Analysis` and `QuantumTheory.ConservationLaw`; second-quantized layers only
supply `dGamma`, bounded-realization, lattice, and response adapters where those are genuinely needed.

## Repository-level dependency direction

The stable repository-level direction is

```text
Analysis, Combinatorics, QuantumTheory
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

The durable CI rules are current-state dependency rules:

- `Analysis`, `Combinatorics`, and `QuantumTheory` do not import `SecondQuantization`;
- `SecondQuantization.Common` does not import `Fermionic` or `Bosonic`;
- statistics-specific layers may consume Common and upstream reusable mathematics/quantum theory.

These rules intentionally do not maintain blacklists of modules, imports, or identifiers that existed
before an earlier refactor.

## Fermionic responsibility DAG

Within the fermionic tree, reusable theory flows downstream through explicit responsibility layers:

```text
Fermionic.Algebra
      ↓
┌───────────────────────────────┐
│ Fermionic.Field               │  basis-independent/dGamma side interface
│ Fermionic.Lattice             │  lattice realization
└───────────────────────────────┘
        ↓
Fermionic.Transport             bounded/Kubo specializations
        ↓
Fermionic.Validation            terminal examples and checks
```

`Field` and `Lattice` are sibling realization layers. Reusable `Algebra` does not depend on either
realization or on downstream consumers. `Field` and `Lattice` do not depend on `Transport` or
`Validation`, and `Transport` does not depend on `Validation`.

The dependency DAG is owned centrally by
`scripts/check_fermionic_transport_validation_boundary.py`. Focused AlgebraicFock and Lattice audits
add domain-specific constraints without duplicating that graph.

## Public import hierarchy

The public import surface mirrors the repository directory hierarchy. Each reusable package has an
umbrella module at the corresponding dotted path, and each parent umbrella imports its immediate
public children instead of flattening all descendant leaves.

```text
SecondQuantization
├── Common
│   ├── Algebra
│   ├── CompletedSpace
│   ├── Diagrammatics
│   ├── ImaginaryTime
│   ├── Interaction
│   ├── Perturbation
│   └── Thermal
├── Fermionic
│   ├── Algebra
│   ├── CompletedSpace
│   ├── Diagrammatics
│   ├── Field
│   ├── ImaginaryTime
│   ├── Lattice
│   ├── Perturbation
│   ├── Thermal
│   ├── Transport
│   └── Validation
└── Bosonic
    ├── Algebra
    ├── Diagrammatics
    ├── ImaginaryTime
    ├── Perturbation
    └── Thermal
```

The full public entry point is

```lean
import LeanCondensedMatter.SecondQuantization
```

A development may stop at any reusable subtree boundary, for example

```lean
import LeanCondensedMatter.SecondQuantization.Common
import LeanCondensedMatter.SecondQuantization.Fermionic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport
```

Implementation modules should still import the narrowest leaf modules they use; umbrellas are public
package boundaries and navigation surfaces, not a reason to widen internal dependencies. When a file
sharing a directory name is itself a semantic base imported by descendants, it remains that base
rather than being turned into an aggregator that would create an import cycle.

One-body generalized current work that does not use second quantization should instead import the
appropriate `Analysis` or `QuantumTheory.ConservationLaw` leaf.

Leaf implementation files are not a compatibility surface. When a routing module ceases to represent
a reusable concept, downstream code should consume the surviving semantic owner rather than keeping a
compatibility layer solely for an old import path.

## Diagrammatics boundary

The current diagrammatic architecture separates reusable combinatorics from statistics-specific
amplitudes.

```text
Combinatorics
  finite partitions / pairings / cumulants
          ↓
SecondQuantization.Common.Diagrammatics
  ordered data / components / reassembly / shuffles / simplex products
          ↓
SecondQuantization.Fermionic.Diagrammatics
  fermionic pair values / signs / Wick amplitudes / Dyson expansions
          ↓
physics-facing connected theorems
```

Common owns component and shuffle structure when no fermionic sign or energy data is required.
Fermionic modules should call those results directly instead of exposing parameter-substitution or
proof-routing wrappers.

`Common.ExternalInsertionDiagram` is the core syntax for higher-point paired diagrams. Its parameter
`E` represents `2 * E` one-legged external insertions, which keeps the total leg count even and
lets the existing ordered `Pairing` API carry fermionic crossing data without a separate parity
witness. At `E = 1` it has the same external/interaction shape as the established two-point
diagram data, but the mature two-point representation remains independent so its definitional
normal forms are preserved. A bridge is introduced only when a concrete higher-point consumer needs
semantic transport between the two representations. Odd external sectors are outside this
paired-diagram representation and should be handled by a separate vanishing statement when a
physical consumer requires them.

The generic external-insertion component layer classifies each connected component as either
externally supported or vacuum. `ExternalInsertionDiagram.HasNoVacuumComponent` requires every
interaction vertex to lie in a component meeting at least one external insertion; it does not require
distinct external insertions to lie in the same component. The finite component partition is the
disjoint union of `externallySupportedComponentParts` and `vacuumComponentParts`.
`ExternalInsertionDiagram.externalPart` extracts the finite subset of external insertion indices
carried by a component, and external support is exactly nonemptiness of that subset. Every component
carries an even number of external insertions, proved from the fixed-point-free restricted
`PairingOn` and the four-leg contribution of each interaction vertex. Its local external sector is
therefore indexed by `Fin (2 * externalPairCount)`; `externalPartOrderIso` gives the canonical
increasing identification with the ambient external subset, preserving external insertion order for
later sign-sensitive constructions. A vacuum component has no external legs, so Common reindexes its
surviving legs as ordinary quartic legs and exposes the induced `QuarticDiagram`; externally
supported component restriction still requires combining this external-sector reindexing with the
interaction-sector restriction.

The two-point expansion has its own internal layer order:

```text
Semantics → Factorization → Analysis → Integration → Series
```

Lower layers must not import higher layers or their umbrella. The checker derives this from parsed
Lean imports rather than source-line regexes.

## Current linked-cluster endpoints

The finite-mode fermionic partition-function line has both formal and analytic linked-cluster
endpoints. The canonical formal endpoint is

```lean
SecondQuantization.Fermionic.
  factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
```

and the finite-dimensional analytic endpoint is

```lean
SecondQuantization.Fermionic.
  iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude
```

The external-leg line has also reached the finite-mode two-point endpoint

```lean
SecondQuantization.Fermionic.
  vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

in `TwoPointDiagramExpansion/Series/CauchySeries.lean`. This means the next correlation-function
target is higher-point/source-insertion structure, not re-proving the two-point linked-cluster
identity.

## Normalized moment and connected-decomposition boundary

The statistics-independent algebraic boundary is owned by `Combinatorics`.
`NormalizedSetFunction` is the canonical normalized finite-set representation,
`powerSeriesMomentSetFunction` packages factorial-normalized coefficients of a unit-constant formal
power series into that representation, and `MultiplicativeWeight` expresses factorization over
connected components. The formal linked-cluster bridge consumes these objects directly.

There is no separate source-functional wrapper in the current API. Pre-normalized external-insertion
moments, Grassmann variables, and arbitrary higher-point source semantics remain downstream research
targets and should introduce a source abstraction only when concrete consumers require one.

## Fermionic field/current boundary

The basis-independent algebraic field architecture is documented separately in
[`fermionic-field-operators.md`](fermionic-field-operators.md). The one-body/current boundary is

```text
Analysis.Operator.LinearCommutator
        ↓
Analysis.Calculus.OneBodyBalance
        ↓
Analysis.Calculus.CurrentRepresentation
        ↓
QuantumTheory.ConservationLaw
        ↓
┌───────────────────────────────┐
│ Fermionic.Field               │  dGamma generalized-quantity bridge
│ Fermionic.Lattice             │  lattice current constructions
└───────────────────────────────┘
        ↓
Fermionic.Transport
```

`Fermionic.Field` remains a narrow side interface for basis-independent density constructions and the
fermionic `dGamma` bridge. It is not a one-body transport umbrella. Generic response, resolvent,
conductivity, and Středa mathematics belongs upstream under `QuantumTheory` or other reusable owners;
`Fermionic.Transport` contains statistics/model-specific bounded adapters and physical current
response specializations.

The generic bounded-current response module must not depend on the conventional current
`1/2 {v,m}`. Conventional-current response is a downstream specialization, so non-conventional
orbital/nonlocal currents can enter through the same arbitrary-current boundary.

## Algebraic Fock operator coordinates

`SecondQuantization.Common.Algebra.AlgebraicFock` owns the reusable occupation-basis coordinate API.
For fixed basis labels, `matrixCoeffLinear m n` is the canonical complex-linear functional on
algebraic-Fock endomorphisms; composition formulas belong there rather than in the trace layer.
Basis-diagonal operators are represented by the algebra homomorphism
`diagonalOperator : (Config → ℂ) →ₐ[ℂ] End`.

Imaginary-time diagonal evolution specializes that algebra representation. Its invertible form is
`diagonalEvolutionEquiv`, and operator Heisenberg evolution is the conjugation algebra equivalence
`(diagonalEvolutionEquiv energy τ).conjAlgEquiv ℂ`. Consumers should use the bundled `map_*`
interface rather than operation-specific forwarding lemmas.

This algebraic coordinate layer is dimension-independent. Ordinary `LinearMap.trace` is only used
for finite configuration types; possibly infinite occupation bases use `tsumTrace` together with
explicit summability hypotheses.

## Finite operator realizations

Finite-dimensional operator transport has two intentionally distinct canonical realizations. Analytic
Dyson and Bochner-integral code uses
`Common.finiteContinuousOperatorAlgEquiv`, which transports algebraic Fock endomorphisms to bounded
operators on `Config → ℂ`. Hilbert-space adjoints and density-operator expectations use
`Common.finiteHilbertOperatorAlgEquiv`, which transports to bounded operators on
`EuclideanSpace ℂ Config`.

Consumers use these bundled algebra equivalences directly, including their standard `map_*` laws.
Representation-specific semantic bridges remain at their owners: basis and coordinate formulas and
the operator-integral compatibility theorem on the analytic side, and basis, adjoint, and
self-adjointness criteria on the Hilbert side. The two realizations are not identified merely because
they are finite-dimensional.

## Free exchange grand-partition boundary

The statistics-independent finite-mode formal grand-product backend is owned upstream by
`QuantumTheory.Gibbs.FreeExchangeCycleSeries`, next to the diagonal one-particle Boltzmann kernel
and the exchange-weighted connected-cycle series. Its grand-product construction is explicitly
restricted to the physical exchange weights `ζ = +1` and `ζ = -1`; the generic permutation
connected-cycle series remains available for arbitrary exchange weight where its stated algebraic
hypotheses hold.

The bosonic and fermionic thermal layers keep only domain-facing specializations of that formal
backend. Fermionic determinant identities remain in the fermionic physical-consumer layer, while
bosonic occupation-space convergence and analytic partition-function results remain in the bosonic
thermal layer. The formal series is never evaluated at `t = 1` as part of this bridge.

## Bosonic boundary

Bosonic algebraic and free thermal results may reuse Common infrastructure, but finite fermionic trace
arguments must not be transferred merely because the mode type is finite. A finite bosonic mode set
still has an infinite occupation basis. Product-domain closure, summability, KMS identities, operator
integration, and Dyson convergence therefore remain explicit analytic obligations of the bosonic
line.

## Refactoring rule

Architecture cleanup should optimize for semantic ownership and API size, not theorem-name length.
Good deletion targets are dead declarations, one-use public wrappers, and modules that contain only a
proof-routing theorem whose proof can be absorbed by its sole consumer with a net code reduction.
Rename-only churn is not an architecture improvement by itself.

When a reusable concept survives, keep it at the narrowest authoritative owner. When only a proof path
survives, keep that path private/local rather than turning it into public API.

Permanent architecture CI should encode the current layer graph, canonical ownership, dimension
boundaries, and semantic safety rules. It should not accumulate a history of removed files, former
owners, or incidental proof syntax.

## CI-enforced invariants

`scripts/check_second_quantization_architecture.py` owns the repository-level SecondQuantization
boundaries:

- path-owned `Common`, `Fermionic`, and `Bosonic` declaration namespaces;
- no statistics-specific imports from `Common`;
- no `SecondQuantization` imports from `Analysis`, `Combinatorics`, or `QuantumTheory`;
- the canonical public SecondQuantization entry point.

`scripts/check_fermionic_transport_validation_boundary.py` owns the fermionic responsibility DAG.
Other focused audits own domain-specific constraints such as algebraic dimension independence,
lattice/response separation, thermal ownership, mode boundaries, density boundaries, and diagrammatic
layer ordering.

Architecture documentation should describe those durable current-state rules. Migration history
belongs in Git history and issue/PR discussion rather than permanent CI assertions.
