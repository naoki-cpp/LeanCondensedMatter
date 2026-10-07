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
operator integration, or diagram sums. `SecondQuantization.Common.OccupationBasis` owns the
statistics-independent total particle-number grade; fermionic and bosonic occupation modules supply
their concrete instances and prove the grade agrees with `Finset.card` and the native `Finsupp.sum`,
respectively.

## Fermionic line

The fermionic algebraic and thermal layers provide CAR/Fock structure, free and interacting
operators, imaginary-time evolution, free Gibbs theory, KMS identities, and Bloch--de Dominicis
pairing. The canonical finite Gibbs pairing endpoint is

```lean
SecondQuantization.Common.BlochDeDominicis.finiteGibbsExpectation_prod_eq_sum_pairing
```

The connected perturbative line proves three finite-mode endpoints:

1. the coefficientwise formal finite-temperature log-partition linked-cluster theorem
   `factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude`;
2. the finite-dimensional analytic log-partition linked-cluster theorem for
   `Tr(exp(-β(H₀ + λV)))`,
   `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_sum_connectedQuarticWickDiagramAmplitude`;
3. the finite-mode two-point theorem
   `vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries`, where the identifier's
   `vacuumNormalized` means normalization by the zero-external-leg Dyson partition series.

The first two names deliberately identify the connected object on the right-hand side as the
quartic Wick-diagram amplitude rather than using a generic `connectedAmplitude` label. The two-point
result already covers one external-leg correlation-function setting. The remaining connected-diagram
target is arbitrary higher-point/source-insertion structure. The reusable normalized algebraic
boundary is `Combinatorics.NormalizedSetFunction` together with
`Combinatorics.powerSeriesMomentSetFunction` and the multiplicative connected-decomposition
machinery. Pre-normalized external-insertion moments, any source-functional API they genuinely
require, and the physical higher-point theorem remain open.

## Diagrammatics ownership

- `Combinatorics/` owns statistics-independent partitions, pairings, cumulants, shuffles, and finite
  product identities;
- `SecondQuantization.Common.Diagrammatics` owns reusable constructions that still carry
  second-quantized/diagrammatic semantics;
- `SecondQuantization.Fermionic.Diagrammatics` owns fermionic signs, amplitudes, and physics-facing
  connected endpoints.

Connected-component factorization theorems use semantic `..._eq_prod_components` names. The
`restrictComponentConnected` construction may still occur inside theorem statements or proofs, but
is not part of the public theorem-name vocabulary.

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
summability and admissible domains explicit. The completed occupation Hilbert space is now exposed as
`Bosonic.CompletedFockSpace Mode`. For finite mode types with positive one-particle energies, the
generic diagonal heat operator is specialized to the free bosonic Hamiltonian, proved trace class,
identified with the existing free partition function, and normalized to the canonical pure-point
Gibbs density operator. The quartic vertex-sequence expansion separately proves free-Gibbs-domain
membership of every finite Dyson coefficient, and the coefficientwise formal linked-cluster theorem
identifies its formal logarithm with connected physical diagrams.

The completed bosonic diagonal sector realizes each single-mode number operator and the free
Hamiltonian as self-adjoint maximal-domain `LinearPMap` operators. Creation and annihilation are
also realized as densely defined closed maximal weighted-shift `LinearPMap` operators on their
natural square-root occupation domains, with creation and annihilation proved to be mutual adjoints.
Both sectors agree with the algebraic operators on the finite-support core. Equal-mode mixed
ladder products have maximal domain `Dom(Nᵢ)` and recover the number operator, its unit shift, and
the completed equal-mode CCR. Ordered quartic vertices are defined on completed Fock space by exact
domain-aware composition of their four ladder operators, and finite quartic interactions are defined
on the dense common intersection of their supported vertex domains with algebraic-core compatibility.
The remaining operator-domain work is to identify useful explicit mixed-mode/quartic weighted
domains and then develop the interacting Hamiltonian/completed-space theory
and all-order Dyson/Taylor convergence (or an explicitly weaker asymptotic/Borel notion where
appropriate).

## Research directions

- pre-normalized time-ordered insertions, higher Green functions, and source derivatives;
- bosonic interacting Dyson convergence and analytic linked-cluster theory;
- explicit bosonic mixed-mode/quartic weighted domains and interacting-Hamiltonian control;
- interacting completed-space fermionic perturbation theory;
- infinite-mode and thermodynamic limits under explicit topological and uniform-estimate hypotheses;
- low-order examples only where they clarify the general theorem rather than create wrapper APIs.
