# Roadmap — Second Quantization (Track D)

Track D develops second quantization as its own construction under
`LeanCondensedMatter/SecondQuantization/`. It supplies the many-body and diagrammatic layer used by
the finite-temperature Linked Cluster Theorem (LCT).

The finite-mode fermionic algebraic LCT is now complete. The next work is no longer missing
combinatorics; it is the analytic interpretation of the formal Dyson series, correlation-function
extensions, and the convergence-aware bosonic line.

See also:

- [`second-quantization-status.md`](second-quantization-status.md) for the current capability matrix;
- [`linked-cluster-theorem.md`](linked-cluster-theorem.md) for the completed M0–M5 proof chain;
- [`../roadmap.md`](../roadmap.md) for the repository-wide target table.

## Scope

The current fermionic theorem is deliberately algebraic and finite-mode:

- `Mode` is finite;
- fermionic occupation states are finite subsets of `Mode`, so the algebraic Fock basis is finite;
- Dyson coefficients are defined by finite-dimensional operator-valued iterated integrals;
- the partition function is packaged as a formal power series;
- no convergence of the full perturbation series is assumed;
- no equality with an analytic interacting partition function is asserted;
- Hilbert-space completion, unbounded operators, trace-class theory, and thermodynamic limits are
  separate later tracks.

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
Linked Cluster Theorem
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

## Fermionic primary line

### Algebraic Fock construction — complete

The fermionic basis is

```lean
Fermionic.Occupation Mode := Finset Mode
```

with algebraic Fock space, signed creation/annihilation operators, CAR, number operators, free
Hamiltonians, and grading all implemented under `Fermionic/Algebra/`.

The finite occupation basis has cardinality `2^|Mode|`, which is the key reason the fermionic line can
support a finite-basis Dyson and trace construction without introducing analytic summability
infrastructure first.

### Imaginary time and thermal theory — complete at the algebraic finite-mode level

Implemented results include:

- basis-diagonal free imaginary-time evolution;
- arbitrary interaction-picture matrix coefficients;
- finite weighted traces and normalized Gibbs expectations;
- free partition and two-point functions;
- grading selection rules and contractions;
- KMS rotation infrastructure;
- the abstract finite-temperature Bloch–de Dominicis pairing theorem and fermionic specializations.

A general many-operator time-ordering API and completed-space analytic formulation remain possible
extensions, but they are not blockers for the proved coefficientwise LCT.

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

### Algebraic Linked Cluster Theorem — complete

The completed M0–M5 sequence is:

| Milestone | Result | Status |
|---|---|---|
| M0 | finite-family component-shuffle ordered-simplex product | complete |
| M1 | fermionic contraction-integrand factorization | complete |
| M2 | complete quartic Wick-amplitude factorization | complete |
| M3 | Dyson finite-set cumulant equals the connected-diagram sum | complete |
| M4 | factorial-normalized formal-log coefficient equals the finite-set cumulant | complete |
| M5 | final Dyson LCT specialization and public export | complete |

The final declaration is

```lean
SecondQuantization.factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
```

and states, for `n ≠ 0`,

```text
n! [λⁿ] log(normalize(dysonPartitionSeries))
  = ∑ connected quartic Wick diagrams on Fin n, amplitude(diagram).
```

The exact proof architecture is documented in
[`linked-cluster-theorem.md`](linked-cluster-theorem.md).

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
`log Ẑ` into finite-set cumulants.

## Formal versus analytic statements

The proved theorem concerns the formal series assembled from the actual coefficientwise Dyson
recursion. It does not yet prove the analytic identity

```text
∑ₙ λⁿ Dₙ(β) = exp(βH₀) exp(-β(H₀ + λV))
```

or the corresponding partition-function identity

```text
Z_D(λ) = Tr(exp(-β(H₀ + λV))).
```

For finite fermionic mode sets these statements should be approachable using finite-dimensional
operator ODEs, matrix exponentials, and analytic Taylor-series uniqueness. They are the next major
fermionic milestone.

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

## Next phases

### F1 — Low-order fermionic verification

Prove explicit `n = 1, 2, 3` corollaries and compare them with enumerated connected diagrams:

```text
1! [λ] log Z = z₁,
2! [λ²] log Z = 2z₂ - z₁²,
3! [λ³] log Z = 6z₃ - 6z₁z₂ + 2z₁³.
```

This provides readable examples and regression coverage for the general theorem.

### F2 — Analytic finite-dimensional Dyson theorem

Establish the interaction-picture evolution equation, convergence of the coefficient series, and
identification with the finite-dimensional matrix exponential. Then connect the formal partition
series to the analytic normalized interacting partition function.

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
