# Roadmap — Second Quantization

Second quantization is developed under `LeanCondensedMatter/SecondQuantization/` as the many-body and
diagrammatic layer used by finite-temperature perturbation theory and the Linked Cluster Theorem.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for the current public API,
  capability matrix, and ownership boundaries;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for the formal and analytic theorem chain;
- [`../roadmap.md`](../roadmap.md) for repository-wide research targets.

## Current boundary

The algebraic foundations allow arbitrary mode types and finite-support states. Full thermal traces,
finite-basis operator integration, quartic diagram sums, and the analytic fermionic partition function
introduce finite-mode or finite-configuration hypotheses explicitly.

The fermionic line proves both the coefficientwise formal Linked Cluster Theorem and its
finite-dimensional analytic partition-function form. These results do not imply completed-space
unbounded-operator theory, trace-class infinite-dimensional Gibbs states, infinite-mode limits, or a
thermodynamic limit.

The bosonic occupation basis is infinite even for finitely many modes. Bosonic perturbation theory
therefore requires explicit summability domains, product closure, KMS control, and a compatible
operator-integration interface.

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
Wick diagram expansion
  ↓
component factorization and cumulants
  ↓
formal and analytic Linked Cluster Theorems
```

The dependency direction is:

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

Responsibility-specific developments should import the narrowest applicable leaf umbrella.

## Fermionic line

### Algebraic and thermal infrastructure

The fermionic basis is

```lean
Fermionic.Occupation Mode := Finset Mode
```

and the algebraic API provides signed creation and annihilation operators, CAR, number operators,
grading, free Hamiltonians, quartic interactions, and imaginary-time evolution.

When `Mode` is finite, the occupation basis is finite. This supports finite weighted traces,
normalized Gibbs expectations, coefficientwise operator integration, and finite-dimensional analytic
operator methods without first introducing trace-class infrastructure.

The thermal layer includes free partition functions, two-point functions, contractions, KMS rotation,
and the finite-temperature Bloch–de Dominicis pairing theorem.

### Quartic diagrams and the formal theorem

The diagrammatic layer provides:

- ordered quartic vertices and local legs;
- pairing data and fermionic crossing signs;
- full Wick-diagram amplitudes;
- the Dyson diagram expansion;
- component restriction, reassembly, and factorization;
- ordered-simplex shuffle products;
- finite-set cumulants and connected-diagram sums.

The formal endpoint is:

```lean
SecondQuantization.Fermionic.
  factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

For `n ≠ 0`, it states schematically:

```text
n! [λⁿ] log(normalized Dyson partition series)
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The factorial converts the ordinary Dyson power-series coefficients into the finite-set normalization
used by moment–cumulant inversion.

### Analytic finite-dimensional theorem

The finite-mode line identifies the Dyson trace series with

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

It proves a Taylor expansion at zero coupling, constructs the local logarithm branch through
`log 1 = 0`, identifies logarithmic derivatives with the formal coefficients, and concludes
schematically that

```text
(dⁿ/dλⁿ)|₀ log(Z(λ) / Z(0))
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

The formal theorem remains useful for coefficient manipulations. The analytic logarithmic derivative
is the physical finite-mode endpoint.

## Bosonic line

The bosonic occupation basis is

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ.
```

Implemented layers include:

- algebraic Fock space and normalized ladder operators;
- CCR, grading, and number operators;
- free imaginary-time evolution and interaction-picture ladder formulas;
- convergent free partition and particle-number sums under explicit positivity assumptions;
- free two-point results and Bloch–de Dominicis base identities;
- `ConvergenceAwareGibbsFunctional`, defined on an explicit summability domain;
- quartic labels, local legs, ordered diagrams, component decomposition, and scalar component
  prefactors.

The Gibbs domain is a linear subspace. Closure under operator products and integrals is not automatic
and must be proved for each perturbative construction.

The next bosonic analytic requirements are:

1. product-domain closure for observables used in Wick recursion;
2. summability-aware KMS rotation and trace cyclicity;
3. an operator-valued integration interface compatible with those domains;
4. convergence control for Dyson coefficients and traces;
5. full Wick amplitudes and a connected-diagram specialization.

## API ownership policy

`Analysis/` and `Combinatorics/` own mathematics that is reusable without occupation-space or
second-quantized semantics. `SecondQuantization.Common` owns statistics-independent constructions
that still depend on Fock operators, exchange statistics, thermal functionals, or diagram data.

A fermionic or bosonic declaration should remain public only when it adds statistics-specific or
physics-facing content. A theorem that merely substitutes an energy, sign convention, or statistics
parameter into a Common result should normally be used directly rather than wrapped.

Proof-only transport lemmas, uniqueness steps, and basis calculations should be private or local.
Module boundaries should follow reusable mathematical or physical concepts, not the order in which a
proof was developed.

## Research directions

### Low-order explicit examples

Derive readable first-, second-, and third-order consequences of the formal and analytic logarithm
identities and compare them with enumerated connected diagrams.

### Correlation functions with external operators

Extend the cumulant and connectedness machinery to time-ordered Green functions and source
insertions, rather than only the partition-function sector.

### Bosonic thermal closure

Prove product-domain membership, normalized two-point and higher recursion results, and
summability-aware KMS identities for the convergence-aware Gibbs functional.

### Bosonic Dyson and connected diagrams

Construct a domain-compatible operator integral, establish Dyson convergence, and reuse the Common
shuffle and cumulant infrastructure for bosonic amplitudes.

### Completed-space and infinite-mode analysis

Develop completed Fock representations, domains and functional calculus for unbounded operators,
trace-class Gibbs states, infinite-mode limits, and thermodynamic limits as separate analytic results.
