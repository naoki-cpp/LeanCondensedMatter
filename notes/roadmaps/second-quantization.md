# Roadmap — Second Quantization (Track D)

Track D develops second quantization as its own construction under
`LeanCondensedMatter/SecondQuantization/`. It supplies the many-body and diagrammatic layer used by
the finite-temperature Linked Cluster Theorem (LCT).

The finite-mode fermionic line now contains both the coefficientwise formal/algebraic LCT and its
finite-dimensional analytic upgrade. The remaining research work is low-order regression coverage,
correlation functions with external legs, convergence-aware bosonic perturbation theory, and later
completed-space or infinite-mode extensions. Canonical API consolidation is tracked separately in
[`second-quantization-refactor.md`](second-quantization-refactor.md) and issue #345.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for the current capability matrix;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for the completed formal and analytic proof
  chain;
- [`second-quantization-refactor.md`](second-quantization-refactor.md) for the breaking canonical-API
  migration;
- [`../roadmap.md`](../roadmap.md) for the repository-wide target table.

## Scope and finiteness boundary

The implementation has two distinct boundaries that should not be conflated.

The following algebraic APIs do not intrinsically require a finite mode or configuration type:

- algebraic Fock vectors, whose individual values have finite support;
- diagonal evolution and interaction-picture matrix-coefficient formulas;
- the Heisenberg-evolution semigroup law;
- fermionic local-leg operators and their CAR/time-evolution identities.

The completed thermal, Dyson, diagrammatic, and analytic fermionic LCT line remains finite-mode:

- `Mode` is finite;
- fermionic occupation states are finite subsets of `Mode`, so the full algebraic Fock basis is
  finite;
- finite weighted traces and Gibbs expectations enumerate that basis;
- the current operator-valued Dyson integration reconstructs operators through finite basis sums;
- quartic vertex labels and diagrams are enumerated by finite sums;
- the analytic partition-function and analytic LCT results use the resulting finite-dimensional
  operator space.

For this finite-mode line, the Dyson coefficient series is proved to converge to the genuine
interacting partition function, and the local analytic logarithm is proved to have connected-diagram
Taylor derivatives. Hilbert-space completion, unbounded operators, trace-class theory, infinite mode
sets, and thermodynamic limits remain separate later tracks.

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
component factorization + cumulants + formal log
  ↓
formal and analytic Linked Cluster Theorems
```

Statistics-independent definitions and proofs live under `SecondQuantization/Common/`. General
analysis and combinatorics live under `Analysis/` and `Combinatorics/`. The dependency direction is

```text
Analysis, Combinatorics
          ↓
SecondQuantization/Common
          ↓
Fermionic, Bosonic
```

The single full public entry point is

```lean
import LeanCondensedMatter.SecondQuantization
```

Responsibility-specific code may instead import a leaf umbrella such as
`LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation`.

## Fermionic primary line

### Algebraic Fock construction — complete

The fermionic basis is

```lean
Fermionic.Occupation Mode := Finset Mode
```

with algebraic Fock space, signed creation/annihilation operators, CAR, number operators, free
Hamiltonians, and grading implemented under `Fermionic/Algebra/`.

When `Mode` is finite, the occupation basis has cardinality `2^|Mode|`. This is the key reason the
fermionic thermal and Dyson line can use finite traces and finite-dimensional operator analysis
without introducing trace-class or summability infrastructure first.

### Imaginary time and thermal theory — complete for the current line

Implemented results include:

- basis-diagonal free imaginary-time evolution;
- arbitrary interaction-picture matrix coefficients, including formulas valid for arbitrary
  configuration types where no full-basis sum is required;
- finite weighted traces and normalized Gibbs expectations;
- free partition and two-point functions;
- grading selection rules and contractions;
- KMS rotation infrastructure;
- the abstract finite-temperature Bloch–de Dominicis pairing theorem and fermionic specializations.

A general many-operator time-ordering API and completed-space analytic formulation remain possible
extensions, but they are not blockers for the completed finite-mode LCT.

### Quartic interaction and Wick diagrams — complete

The non-diagonal quartic interaction used by the Dyson/Wick line is implemented in
`Fermionic/Diagrammatics/QuarticInteraction.lean` and has the schematic form

```text
V = ∑ᵢⱼₖₗ g(i,j,k,l) cᵢ† cⱼ† cₖ cₗ.
```

The diagrammatic layer contains:

- ordered quartic vertices and local legs;
- pairing data and fermionic crossing signs;
- full quartic Wick-diagram amplitudes;
- the Dyson vertex-moment diagram expansion;
- connected components and component restriction/reassembly;
- component-local vertex orders and global component shuffles.

The local-leg algebra itself no longer requires `[Fintype Mode]`; finiteness enters later when the
full thermal trace, label family, and diagram family are enumerated.

### Formal/algebraic Linked Cluster Theorem — complete

The completed M0–M5 sequence is:

| Milestone | Result | Status |
|---|---|---|
| M0 | finite-family component-shuffle ordered-simplex product | complete |
| M1 | fermionic contraction-integrand factorization | complete |
| M2 | complete quartic Wick-amplitude factorization | complete |
| M3 | Dyson finite-set cumulant equals the connected-diagram sum | complete |
| M4 | factorial-normalized formal-log coefficient equals the finite-set cumulant | complete |
| M5 | final formal Dyson LCT specialization | complete |

The final formal declaration is

```lean
SecondQuantization.Fermionic.
  factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and states, for `n ≠ 0`,

```text
n! [λⁿ] log(normalize(dysonPartitionSeries))
  = ∑ connected quartic Wick diagrams on Fin n, amplitude(diagram).
```

The exact diagrammatic proof architecture is documented in
[`linked-cluster-theorem.md`](linked-cluster-theorem.md).

### Analytic finite-dimensional upgrade — complete

The finite-mode line also identifies the formal coefficients with the genuine finite-dimensional
interacting partition function

```text
Z(λ) = Tr(exp(-β(H₀ + λV))).
```

The completed analytic chain includes:

- `hasSum_dysonTraceCoeff_eq_analyticDysonPartitionFunction`, identifying the Dyson trace series with
  `Z(λ)`;
- `hasFPowerSeriesAt_analyticDysonPartitionFunction`, packaging the same coefficients as the Taylor
  series at zero coupling;
- `analyticAt_analyticNormalizedLogPartitionFunction_zero`, selecting the local analytic logarithm
  through `log 1 = 0`;
- `iteratedDeriv_analyticNormalizedLogPartitionFunction_eq_factorial_mul_formalCoeff`, connecting
  analytic logarithmic derivatives to the formal logarithm coefficients;
- `iteratedDeriv_log_normalizedAnalyticPartitionFunction_eq_sum_connectedAmplitude`, identifying
  those derivatives with connected quartic Wick-diagram amplitudes.

Thus, for `n ≠ 0`, the analytic endpoint states schematically

```text
(dⁿ/dλⁿ)|₀ log(Z(λ) / Z(0))
  = ∑ connected n-vertex quartic Wick diagrams, amplitude(diagram).
```

This result is analytic in coupling but still finite-mode and finite-dimensional. It does not imply a
thermodynamic limit or a completed-space treatment of unbounded operators.

## Why the factorial appears

`dysonPartitionSeries` is an ordinary power series

```text
Ẑ(λ) = ∑ₙ zₙ λⁿ.
```

Finite-set partition combinatorics is naturally exponential-generating:

```text
Ẑ(λ) = ∑ₙ mₙ λⁿ / n!.
```

Therefore

```text
mₙ = n! zₙ.
```

`dysonVertexMoment` implements this conversion on a labelled finite set `S`:

```text
dysonVertexMoment(S) = |S|! · normalizedDysonPartitionCoeff(|S|).
```

`Combinatorics/PowerSeriesCumulant.lean` proves that the same normalization converts coefficients of
`log Ẑ` into finite-set cumulants. The analytic bridge then identifies these factorial-normalized
formal coefficients with derivatives of the local analytic logarithm.

## Formal versus analytic statements

The formal theorem and analytic theorem serve different purposes.

The formal theorem is coefficientwise and purely algebraic once the finite Dyson coefficients and
diagram amplitudes are available. It is the reusable combinatorial core and does not itself require a
convergence statement.

The analytic theorem uses the finite-dimensional Common Dyson evolution and trace API to prove
convergence for every coupling, identify the resulting sum with the matrix exponential, and transfer
the formal connected-diagram coefficient identity to derivatives of the genuine normalized
partition-function logarithm near zero coupling.

Both layers remain public: the formal layer is useful for coefficient manipulations and reuse, while
the analytic layer is the physical finite-mode endpoint.

## Bosonic parallel line

The bosonic occupation basis is

```lean
Bosonic.Occupation Mode := Mode →₀ ℕ.
```

Even for finite `Mode`, this type is infinite. The bosonic line therefore mirrors the algebraic and
statistics-independent layers but cannot reuse the finite-basis trace and operator-integral APIs
unchanged.

### Completed bosonic layers

- algebraic Fock space and normalized ladder operators;
- CCR and number operators;
- free imaginary-time evolution and interaction-picture ladder formulas;
- convergent free partition sums under `0 < β εᵢ` assumptions;
- free two-point functions and a two-point Bloch–de Dominicis specialization;
- quartic vertex data, local legs, ordered diagrams, connected components, component decomposition,
  and scalar component prefactors.

### Remaining bosonic blockers

1. **Arbitrary Gibbs functionals.** Existing convergence proofs are expression-specific. A reusable
   functional must carry summability or domain hypotheses.
2. **Operator-valued integration.** The current Common construction uses finite output-basis sums.
3. **Full Wick amplitude and Dyson expansion.** These depend on the preceding two analytic interfaces.
4. **Bosonic LCT specialization.** The Common component-shuffle, formal-log, and abstract connectedness
   results are reusable once a valid bosonic weighted-diagram family exists.

No false `[Fintype (Bosonic.Occupation Mode)]` assumption should be introduced to close these gaps.

## Active canonical-API refactor

Issue #345 is consolidating SecondQuantization around one authoritative owner for each construction.
The canonical entry point, namespace ownership, fermionic core names, bosonic algebra layout, and the
main discrete/continuous Dyson wrapper removals are already in place. Remaining packages continue the
Common-wrapper audit, make the analytic finite-mode result the public perturbative endpoint, simplify
proof-internal module boundaries where useful, and finish documentation and migration validation.

The detailed migration state and removed names are maintained in
[`second-quantization-refactor.md`](second-quantization-refactor.md).

## Next phases

### F1 — Low-order fermionic verification

Prove explicit `n = 1, 2, 3` corollaries and compare them with enumerated connected diagrams:

```text
1! [λ] log Z = z₁,
2! [λ²] log Z = 2z₂ - z₁²,
3! [λ³] log Z = 6z₃ - 6z₁z₂ + 2z₁³.
```

These provide readable examples and regression coverage for both the formal and analytic theorems.

### F2 — Analytic finite-dimensional Dyson theorem — complete

The interaction-picture analytic Dyson evolution, convergence of its coefficient series,
identification with the finite-dimensional matrix exponential and partition function, and transfer to
an analytic connected-diagram theorem are implemented. Future work should build on this result rather
than treating the analytic connection as pending.

### F3 — Correlation functions and external legs

Define source or external-operator insertions and prove that logarithms/cumulants select connected
contributions for time-ordered Green functions, not only the vacuum/free-energy sector.

### B1 — Convergence-aware bosonic functional interface

Design the smallest reusable summability-restricted class that supports linearity, normalization, KMS
rotation, and the required Wick contractions.

### B2 — Bosonic Dyson and diagram expansion

Build an operator-integral interface compatible with the bosonic functional, then instantiate the
existing Common diagram and cumulant machinery.

### A1 — Completed-space and infinite-mode extensions

After suitable trace-class and unbounded-operator infrastructure exists, study infinite mode sets,
Hilbert-space completion, and thermodynamic limits as separate analytic results.
