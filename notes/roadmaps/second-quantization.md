# Roadmap — Second Quantization

Second quantization is developed under `LeanCondensedMatter/SecondQuantization/` as the many-body,
thermal, perturbative, and diagrammatic layer of LeanCondensedMatter.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for the current public API and ownership boundaries;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for the vacuum and two-point connected-diagram endpoints;
- [`completed-space-and-infinite-mode.md`](completed-space-and-infinite-mode.md) for completed-space and infinite-mode boundaries;
- [`../roadmap.md`](../roadmap.md) for repository-wide targets.

## Current boundary

The algebraic foundations allow arbitrary mode types and finite-support states. Finite thermal traces,
finite-basis operator integration, and the current fermionic Dyson/diagrammatic theorems introduce
finite-mode assumptions explicitly.

The fermionic line now proves three connected perturbative endpoints:

1. a coefficientwise formal vacuum Linked Cluster Theorem;
2. a finite-dimensional analytic vacuum Linked Cluster Theorem for the interacting partition function;
3. a finite-mode two-point Linked Cluster Theorem stating that vacuum normalization leaves exactly
   externally connected two-point diagrams.

These results do not imply trace-class infinite-dimensional Gibbs states, general unbounded-operator
theory, arbitrary multi-leg/source-insertion expansions, infinite-mode thermal limits, or a
thermodynamic limit.

The bosonic occupation basis remains infinite even for finitely many modes, so bosonic perturbation
theory requires explicit summability and domain control rather than reuse of finite-configuration
fermionic trace arguments.

## Architecture

```text
Mode
  ↓
occupation representation
  ↓
algebraic Fock space
  ↓
creation / annihilation operators
  ↓
CAR or CCR
  ↓
free and interacting operators
  ↓
imaginary-time evolution and thermal functionals
  ↓
Dyson coefficients
  ↓
Wick / two-point diagram expansions
  ↓
component factorization and connectedness
  ↓
formal, analytic, and two-point linked-cluster theorems
```

Dependency direction:

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

The full public import is:

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific developments should import the narrowest applicable stable umbrella.

## Fermionic line

The algebraic API provides occupation-space creation and annihilation operators, CAR, number
operators, grading, free Hamiltonians, quartic interactions, and imaginary-time evolution. For finite
`Mode`, the occupation basis is finite, which supports finite weighted traces and finite-dimensional
operator methods.

The thermal layer includes free partition functions, two-point functions, contractions, KMS rotation,
and the finite-temperature Bloch–de Dominicis pairing theorem.

### Vacuum linked-cluster theorem

The formal endpoint is

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and schematically states

```text
n! [λⁿ] log(normalized Dyson partition series)
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The finite-dimensional analytic endpoint is

```lean
iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

for the genuine interacting partition function

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

### Two-point linked-cluster theorem

The two-point diagram expansion introduces two external legs together with quartic interaction
vertices. The proof separates the unique externally connected component from vacuum components,
reindexes fixed external-slot fibers, proves the coefficientwise Cauchy factorization, and cancels the
normalized vacuum series.

The endpoint is

```lean
vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from
`Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean`.

Schematically,

```text
(two-point Dyson series) / (vacuum Dyson series)
  = ∑ externally connected two-point diagrams.
```

This is already an external-leg connected expansion; the remaining external-operator research target
is the general multi-leg/source-insertion theory, not the two-point case.

## Diagrammatics ownership and API policy

The diagrammatics tree has been consolidated so that proof-routing structure is not automatically a
public API. The intended ownership is:

- `Combinatorics/`: statistics-independent partitions, pairings, slot shuffles, finite products, and
  related reusable finite combinatorics;
- `SecondQuantization.Common.Diagrammatics`: statistics-independent constructions that still carry
  diagram/Fock/thermal semantics;
- `SecondQuantization.Fermionic.Diagrammatics`: fermionic amplitudes, signs, physical specializations,
  and linked-cluster endpoints.

One-use routing theorems and modules should be inlined or made private/local when doing so reduces code
without obscuring a reusable concept. Compatibility aliases are not kept solely to preserve internal
proof history.

## Completed fermionic representation

The completed space

```lean
Fermionic.CompletedFockSpace Mode := ℓ²(Fermionic.Occupation Mode, ℂ)
```

has canonical basis vectors, an injective dense algebraic inclusion, and a bounded single-mode number
projection. Completed ladder operators, unbounded Hamiltonian domains, completed Gibbs states, and
infinite-mode perturbation theory remain separate analytic work.

## Bosonic line

The bosonic occupation basis is

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ.
```

Implemented layers include algebraic Fock/CCR infrastructure, free imaginary-time evolution,
convergent free thermal sums under explicit positivity assumptions, a convergence-aware Gibbs
functional, and statistics-independent diagrammatic infrastructure reusable from Common.

The next bosonic analytic requirements are product-domain closure, summability-aware KMS/cyclicity,
a compatible operator-valued integration interface, Dyson convergence, and full connected-diagram
specialization.

## Research directions

### Higher correlation functions and sources

Generalize the proved two-point external-leg theorem to arbitrary time-ordered insertions, source
derivatives, higher Green functions, and multi-leg connected diagrams.

### Low-order explicit examples

Use low-order expansions as readable regression examples where they expose the general theorem, but do
not add wrapper theorems that merely specialize a generic result without semantic value.

### Bosonic thermal closure and Dyson theory

Build the summability/domain infrastructure required for a convergence-aware bosonic linked-cluster
line.

### Completed and infinite-mode theory

Construct bounded completed CAR operators, weighted domains for unbounded operators, trace-class Gibbs
states under explicit hypotheses, and eventually well-specified infinite-mode or thermodynamic limits.
