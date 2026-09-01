# Second Quantization — current status

Lean declarations and CI-enforced dependency checks are the source of truth. This page summarizes
stable public ownership and proved endpoints.

## Public structure

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

The full public import is

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific developments should use the narrowest stable umbrella. Reusable finite
combinatorics belongs in `Combinatorics`; statistics-independent Fock/thermal/diagrammatic structure
belongs in `SecondQuantization.Common`; statistics-specific or physics-facing endpoints belong in the
Fermionic or Bosonic layers. Proof-only routing and one-use reindexing helpers should not become
public API.

## Fermionic algebraic and thermal line

The algebraic foundations allow arbitrary mode types with finite-support states. The fermionic line
contains CAR/Fock infrastructure, free Hamiltonians and interactions, imaginary-time evolution, free
Gibbs theory, KMS identities, and the finite-temperature Bloch--de Dominicis pairing theorem.

Finite mode assumptions enter where the theory enumerates all occupations, uses finite-dimensional
trace/operator integration, or forms finite diagram sums.

## Fermionic connected-diagram endpoints

Three finite-mode endpoints are proved:

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

for the coefficientwise formal vacuum linked-cluster theorem,

```lean
iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

for the finite-dimensional analytic vacuum theorem, and

```lean
vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

for the two-external-leg linked-cluster theorem.

The general higher-point/source-insertion connected expansion remains open.

## Completed fermionic representation

```lean
Fermionic.CompletedFockSpace Mode := ℓ²(Fermionic.Occupation Mode, ℂ)
```

is implemented with a dense algebraic core, bounded number/creation/annihilation operators, completed
CAR, maximal diagonal unbounded operators with explicit `LinearPMap` domains, analytic properties of
real diagonal operators, product-domain/free-Hamiltonian ladder results, finite-dimensional
compatibility, and finite-mode truncations.

Completed free-fermion thermal specializations live under `Fermionic.Thermal.Completed`. They reuse
the generic pure-point Gibbs state, provide summability-controlled expectations, KMS and pairing
recursion data, and prove finite-mode Gibbs convergence against bounded observables.

This does not provide interacting completed-space Dyson theory or a thermodynamic limit.

## Bosonic boundary

Even for finite `Mode`,

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ
```

is infinite. The bosonic line therefore uses explicit summability domains. Algebraic CCR,
imaginary-time evolution, convergent free thermal sums, a convergence-aware Gibbs functional, and
reusable Common diagrammatics are available, but a full bosonic Dyson/linked-cluster theory still
requires product-domain closure, summability-aware KMS/cyclicity, operator-valued integration, and
convergence control.

## Open work

- higher time-ordered correlation functions and arbitrary source/multi-leg insertions;
- convergence-aware bosonic Dyson and connected-diagram theory;
- completed bosonic operator/domain theory;
- interacting completed-space fermionic perturbation theory;
- infinite-volume and thermodynamic limits with explicit analytic hypotheses;
- continued removal of public declarations that serve only proof routing.
