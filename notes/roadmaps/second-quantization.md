# Second Quantization roadmap

Second quantization is the many-body, thermal, perturbative, and diagrammatic layer under
`LeanCondensedMatter/SecondQuantization/`.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for current ownership and proved endpoints;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for connected-diagram results;
- [`completed-space-and-infinite-mode.md`](completed-space-and-infinite-mode.md) for completed-space boundaries.

## Architecture

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

The algebraic foundations support arbitrary mode types with finite-support states. Finiteness enters
only where a theorem explicitly enumerates modes/configurations or uses finite-dimensional trace,
operator integration, or diagram sums.

## Fermionic line

The fermionic algebraic and thermal layers provide CAR/Fock structure, free and interacting
operators, imaginary-time evolution, free Gibbs theory, KMS identities, and Bloch--de Dominicis
pairing.

The connected perturbative line proves:

1. the coefficientwise formal vacuum linked-cluster theorem;
2. the finite-dimensional analytic vacuum linked-cluster theorem for
   `Tr(exp(-β(H₀ + λV)))`;
3. the finite-mode two-point theorem
   `vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries`.

The two-point result already covers one external-leg correlation-function setting. The remaining
connected-diagram target is arbitrary higher-point/source-insertion structure.

## Diagrammatics ownership

- `Combinatorics/` owns statistics-independent partitions, pairings, cumulants, shuffles, and finite
  product identities;
- `SecondQuantization.Common.Diagrammatics` owns reusable constructions that still carry
  second-quantized/diagrammatic semantics;
- `SecondQuantization.Fermionic.Diagrammatics` owns fermionic signs, amplitudes, and physics-facing
  connected endpoints.

One-use routing theorems, reindexings, and intermediate proof stages should remain private/local or be
inlined rather than exposed as parallel public APIs.

## Completed fermionic line

`Fermionic.CompletedFockSpace Mode := ℓ²(Fermionic.Occupation Mode, ℂ)` has bounded completed ladder
operators and CAR, explicit domains for unbounded diagonal operators, free-Hamiltonian domain/ladder
results, finite-dimensional compatibility, and finite-mode truncations.

`Fermionic.Thermal.Completed` adds the summability-controlled free Gibbs/KMS/pairing route and
finite-mode Gibbs convergence against bounded observables. Interacting completed-space Dyson theory
and thermodynamic limits remain open.

## Bosonic line

The bosonic occupation basis is infinite even for finite mode types. Existing results therefore keep
summability and admissible domains explicit. Algebraic CCR structure, free thermal sums, a
convergence-aware Gibbs functional, and reusable diagrammatic infrastructure are available.

A full bosonic perturbative line still needs product-domain closure, summability-aware KMS/cyclicity,
operator integration, Dyson convergence, and connected-diagram specialization.

## Research directions

- arbitrary time-ordered insertions, higher Green functions, and source derivatives;
- convergence-aware bosonic Dyson and linked-cluster theory;
- completed bosonic Fock/operator-domain theory;
- interacting completed-space fermionic perturbation theory;
- infinite-mode and thermodynamic limits under explicit topological and uniform-estimate hypotheses;
- low-order examples only where they clarify the general theorem rather than create wrapper APIs.
