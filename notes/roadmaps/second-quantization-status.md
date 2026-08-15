# Second Quantization — Current Status

This page summarizes the current architecture and proved endpoints under
`LeanCondensedMatter/SecondQuantization/`. Lean declarations and CI-enforced dependency checks are
the source of truth.

## Scope and current boundary

The algebraic foundations are not intrinsically finite-mode: fermionic occupations are finite
subsets, bosonic occupations are finitely supported functions, and algebraic Fock vectors are finite
linear combinations. Finiteness enters when a theorem enumerates all modes/configurations or uses a
finite-dimensional trace, operator integral, or diagram sum.

The fermionic line is currently proved through:

- algebraic CAR/Fock infrastructure and finite-temperature free Gibbs theory;
- the finite-temperature Bloch–de Dominicis pairing theorem;
- Dyson coefficients and finite-dimensional analytic Dyson evolution;
- quartic Wick/Dyson diagrams and connected component factorization;
- the formal vacuum Linked Cluster Theorem;
- the finite-dimensional analytic vacuum Linked Cluster Theorem;
- the finite-mode two-point linked-cluster theorem with two external legs.

The two-point endpoint is

```lean
SecondQuantization.Fermionic.
  vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

from `Fermionic/Diagrammatics/TwoPointDiagramExpansion/CauchySeries.lean`. It states that the
vacuum-normalized two-point Dyson series is exactly the series of externally connected two-point
Wick diagrams.

This does not yet provide arbitrary multi-leg/source-insertion connected expansions,
thermodynamic limits, or completed-space interacting Gibbs theory.

## Canonical public imports

The full public entry point is:

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code should prefer the narrowest stable umbrella:

| Area | Common import | Fermionic import | Bosonic import |
|---|---|---|---|
| Algebra | `LeanCondensedMatter.SecondQuantization.Common.Algebra` | `LeanCondensedMatter.SecondQuantization.Fermionic.Algebra` | `LeanCondensedMatter.SecondQuantization.Bosonic.Algebra` |
| Imaginary time | `LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime` | `LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime` |
| Thermal theory | `LeanCondensedMatter.SecondQuantization.Common.Thermal` | `LeanCondensedMatter.SecondQuantization.Fermionic.Thermal` | `LeanCondensedMatter.SecondQuantization.Bosonic.Thermal` |
| Perturbation | `LeanCondensedMatter.SecondQuantization.Common.Perturbation` | `LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation` | not exposed as a full Dyson layer yet |
| Diagrammatics | `LeanCondensedMatter.SecondQuantization.Common.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics` | `LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics` |
| Completed fermionic space | — | `LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace` | — |

## Ownership and dependency direction

```text
Analysis, Combinatorics
          ↓
SecondQuantization.Common
          ↓
SecondQuantization.Fermionic, SecondQuantization.Bosonic
```

`Analysis/` owns reusable analytic and linear-algebraic infrastructure. `Combinatorics/` owns
statistics-independent finite combinatorics such as partitions, pairings, cumulants, slot shuffles,
and product identities when they do not require second-quantized semantics.

`SecondQuantization.Common` owns statistics-independent structures that still depend on Fock,
thermal, or diagrammatic semantics. `Fermionic` and `Bosonic` should expose declarations only when
they add statistics-specific or physics-facing content.

Recent diagrammatics cleanup deliberately removed one-use routing modules and public wrappers. The
current policy is:

- reusable combinatorics belongs in `Combinatorics`;
- reusable statistics-independent diagrammatics belongs in `SecondQuantization.Common`;
- physics-facing fermionic endpoints remain public in `SecondQuantization.Fermionic`;
- proof-only transports, reindexings, uniqueness facts, and one-use wrappers should be private/local
  or inlined when that reduces code without hiding a reusable domain concept;
- file boundaries should correspond to reusable concepts, not merely intermediate proof stages.

The architecture is checked by the SecondQuantization audit and repository architecture scripts.

## Fermionic proved endpoints

### Vacuum/free-energy sector

The coefficientwise formal endpoint is

```lean
factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

which identifies `n! [λⁿ] log Ẑ_D` with connected quartic Wick-diagram amplitudes.

The finite-dimensional analytic endpoint is

```lean
iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude
```

which identifies derivatives at zero coupling of the local normalized logarithm of the genuine
interacting partition function with connected diagram sums.

### Two-point sector

The two-point diagram line defines fixed-external two-point diagrams, their connected external
component, vacuum components, component-local amplitudes, external-slot fibers, and the associated
Cauchy-product factorization. The final power-series cancellation theorem is

```lean
vacuumNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
```

under the finite-mode hypotheses and `0 ≤ β` used by the coefficientwise theorem.

Intermediate routing layers are intentionally not part of the stable API. Public declarations should
be the physical/combinatorial endpoints needed by downstream developments.

## Completed fermionic representation

`Fermionic.CompletedFockSpace Mode := ℓ²(Fermionic.Occupation Mode, ℂ)` is implemented with canonical
basis vectors, an injective dense algebraic core, and a bounded single-mode number projection.
Completed creation/annihilation operators, general unbounded Hamiltonian domains, trace-class Gibbs
states, and infinite-mode thermal limits remain separate work.

## Bosonic boundary

Even for finite `Mode`, the bosonic occupation basis is infinite. The bosonic line therefore uses
explicit summability domains and currently proves algebraic/thermal results only where those domains
are controlled. A general bosonic Dyson/linked-cluster line still requires product-domain closure,
summability-aware KMS/cyclicity, operator-valued integration, and convergence control.

## Current next steps

The finite-mode fermionic vacuum and two-point connected expansions are now base infrastructure.
Separate follow-up tracks include:

1. higher time-ordered correlation functions and arbitrary source/multi-leg insertions;
2. convergence-aware bosonic Dyson and connected-diagram theory;
3. completed bounded CAR operators and unbounded Hamiltonian domains;
4. trace-class/infinite-mode Gibbs states and thermodynamic limits;
5. continued API consolidation where public declarations are only proof-routing artifacts.
