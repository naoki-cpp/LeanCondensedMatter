# Roadmap — Fermionic Linked Cluster Theorem

This page is the execution plan for the finite-mode, finite-temperature fermionic Linked Cluster
Theorem (LCT). It complements the historical narrative in
[`second-quantization.md`](second-quantization.md) and the architecture summary in
[`second-quantization-status.md`](second-quantization-status.md).

The target is an algebraic/formal theorem. It does not claim convergence of the perturbation series,
Hilbert-space completion, or equality with an analytic interacting partition function.

## Target statement

For nonzero perturbation order `n`, the intended final theorem has the shape

```lean
theorem factorial_mul_coeff_dysonFormalLogPartitionFunction_eq_sum_connectedAmplitude
    (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℂ) *
      PowerSeries.coeff n
        (dysonFormalLogPartitionFunction ε β (quarticInteraction g))
    =
    ∑ d : ConnectedQuarticWickDiagram Mode n Finset.univ,
      quarticWickDiagramAmplitude ε β g d
```

The left side is the exponential-generating normalization of a coefficient of normalized formal
Dyson `log Z`. The right side is the sum of amplitudes of connected quartic Wick diagrams on the
labelled vertex set `Finset.univ : Finset (Fin n)`.

## Milestone overview

| Milestone | Deliverable | Status | Depends on | Expected PRs |
|---|---|---|---|---:|
| M0 | Statistics-independent component-shuffle product calculus | complete | — | completed in PRs #233–#247 |
| M1 | Fermionic contraction-integrand factorization | complete | M0 | completed through PR #256 |
| M2 | Full quartic Wick-amplitude factorization | next | M1 | 1 |
| M3 | Connected-diagram formula for `dysonVertexCumulant` | blocked by M2 | M2 | 1–2 |
| M4 | Finite-set cumulant / formal-`log` EGF bridge | independent high-risk track | normalized power-series API | 1–2 |
| M5 | Final Dyson LCT specialization and public export | blocked by M3 and M4 | M3, M4 | 1 |

The remaining implementation is approximately four to six focused PRs. M4 is the main independent
high-risk milestone; M2 should now be a short assembly PR using the completed M0 and M1 results.

## M0 — Component-shuffle product calculus

**Status: complete.**

This milestone established the statistics-independent combinatorics and ordered-simplex analysis
needed to multiply all connected-component contributions.

### Completed foundation

- Global vertex orders decompose into component-local orders and a
  `QuarticDiagram.ComponentShuffle`.
- Recursive binary shuffles are equivalent to ambient two-block slot shuffles:

  ```lean
  BinaryShuffle m n ≃ BinaryShuffle.SlotShuffle m n
  ```

- Two-block ambient integrands satisfy the ordered-simplex product identity.
- `FamilySlotShuffle` represents an arbitrary finite family of ordered slot blocks.
- A family shuffle on `Fin (k + 1)` decomposes into a head-versus-tail binary shuffle and a tail
  family shuffle.
- Finite-family shuffles transport to `QuarticDiagram.ComponentShuffle` through a canonical
  enumeration of connected components.

### Exit theorem

```lean
QuarticDiagram.sum_componentShuffle_orderedSimplexIntegral_eq_prod
```

with theorem shape

```lean
∑ shuffle : d.ComponentShuffle,
    orderedSimplexIntegral S.card β
      (d.componentShuffleIntegrand shuffle componentIntegrand)
  =
  ∏ B : d.componentPartition.parts,
    orderedSimplexIntegral (B : Finset (Fin N)).card β
      (componentIntegrand B)
```

The binary and finite-family sequence was completed by PRs #237–#247. The component-order and
component-integrand infrastructure was completed in PRs #233–#235.

## M1 — Fermionic contraction-integrand factorization

**Status: complete.**

For an assembled global vertex order, the Wick contraction integrand is the product of the
connected-component contraction integrands evaluated on component-restricted times.

### Exit theorem

```lean
QuarticWickDiagram.contractionIntegrand_assembleVertexOrder_eq_prod_components
```

with theorem shape

```lean
d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) τ =
  ∏ B : d.componentPartition.parts,
    QuarticWickDiagram.contractionIntegrand ε β
      (d.restrictComponentConnected B.2).1 (orders B)
      (d.componentTimeAssignment shuffle τ B)
```

### Completed foundation

- The assembled global pairing and ordered legs restrict compatibly to every connected component.
- Every assembled global pair value agrees with its component-local pair value.
- The product over assembled global normalized pairs reindexes as a product over components and
  component-local normalized pairs.
- The fermionic pairing weight factors over components for every component shuffle.
- Cross-component crossing parity is even because each inverted pair of quartic vertex blocks
  contributes `4 × 4 = 16` ordered-leg inversions.
- The two component products combine directly into the full fixed-order contraction integrand.

### Work packages

#### M1a — Pairing restriction and local pair values — complete

Proved that:

1. the global `pairingInOrder` pair set decomposes into component-local pair sets;
2. the global leg operators agree with restricted component leg operators;
3. every global pair value agrees with its restricted component pair value.

#### M1b — Product reindexing — complete

The product over global pairs is reindexed as a product over components and local pairs using
explicit equivalences of pair index types.

#### M1c — Fermionic pairing-sign factorization — complete

`Pairing.weight` factors over connected components under the assembled order. The proof uses the
special permutation induced by shuffling blocks of four vertex legs: a vertex-block transposition
exchanges `4 × 4 = 16` leg pairs, so its cross-component parity contribution is even.

### Definition of done

M1 is complete: the full contraction-integrand theorem is available without adding a new sign
convention or changing `pairingInOrder`.

## M2 — Full quartic Wick-amplitude factorization

**Status: next.**

Combine:

- M1 contraction-integrand factorization;
- the M0 component-shuffle ordered-simplex product theorem;
- the existing coupling-weight and Dyson-sign factorization.

### Exit theorem

```lean
quarticWickDiagramAmplitude ε β g d =
  ∏ B : d.componentPartition.parts,
    quarticWickDiagramAmplitude ε β g
      ((d.restrictComponentConnected B.2).1)
```

This should be a short assembly PR. New combinatorics appearing here indicates that M1 is incomplete.

## M3 — Connected-diagram formula for finite-set cumulants

**Status: blocked by M2.**

Instantiate the existing abstract `Combinatorics.WeightedDiagramFamily` with

```lean
Diagram S          := QuarticWickDiagram Mode N S
ConnectedDiagram S := ConnectedQuarticWickDiagram Mode N S
diagramWeight       := quarticWickDiagramAmplitude ε β g
connectedWeight     := quarticWickDiagramAmplitude ε β g
```

using the existing component-decomposition equivalence and M2 amplitude factorization.

Combine the abstract diagram-connectedness theorem with the Dyson diagram expansion.

### Exit theorem

```lean
dysonVertexCumulant ε β (quarticInteraction g) S =
  ∑ d : ConnectedQuarticWickDiagram Mode N S,
    quarticWickDiagramAmplitude ε β g d
```

for nonempty `S`.

This milestone may need one infrastructure PR for the concrete family instance and one theorem PR,
but they should be combined when elaboration remains straightforward.

## M4 — Finite-set cumulant / formal-log EGF bridge

**Status: not started; independent high-risk track.**

Prove a general theorem for an arbitrary normalized power series, independent of second
quantization.

### Target theorem shape

```lean
(n.factorial : ℂ) * PowerSeries.coeff n (formalLogPartitionFunction Z) =
  Finpartition.cumulantFromMoment
    (fun S => (S.card.factorial : ℂ) * PowerSeries.coeff S.card Z)
    Finset.univ
```

under `PowerSeries.constantCoeff Z = 1` and `n ≠ 0`.

### Required bridge

The proof must align:

- ordinary power-series multiplication and substitution;
- ordered compositions appearing in powers of `Z - 1`;
- labelled set partitions and multinomial factors;
- the Möbius coefficients used by `Finpartition.cumulantFromMoment`.

A clean route is to prove the labelled exponential formula first and then obtain the logarithm theorem
by inversion. A direct coefficient expansion is acceptable only if the resulting API remains reusable
outside the Dyson specialization.

### Definition of done

The theorem lives in `Analysis/` or `Combinatorics/`, mentions no Fock-space or diagrammatic type, and
handles the factorial normalization once rather than in the final LCT proof.

## M5 — Final Dyson LCT specialization

**Status: blocked by M3 and M4.**

Specialize M4 to

```lean
normalizePartitionSeries (dysonPartitionSeries ε β (quarticInteraction g))
```

identify the induced finite-set moment with `dysonVertexMoment`, then compose with M3.

### Exit deliverables

- the target LCT theorem at the top of this document;
- export through the Fermionic public API;
- concise documentation of the algebraic scope and normalization conventions.

This PR should contain little new combinatorics. It should mainly rewrite and combine previously
proved theorems.

## Next PR sequence

The current recommended sequence is:

1. complete quartic Wick-amplitude factorization from M0 and M1;
2. concrete `WeightedDiagramFamily` and connected-diagram finite-set cumulant theorem;
3. general EGF / finite-set cumulant bridge, possibly split into two PRs;
4. final Dyson specialization and API export.

M4 can be developed in parallel with M2–M3 because the two tracks meet only at M5.

## Definition of done

The algebraic fermionic LCT milestone is complete when:

- the target theorem is exported by the Fermionic API;
- it assumes finite `Mode`, the existing ordering/typeclass hypotheses, and `n ≠ 0`, but no analytic
  convergence of the perturbation series;
- all intermediate theorems compile without `sorry`;
- the result uses the existing `quarticWickDiagramAmplitude` without changing its sign or factorial
  conventions;
- repository-wide Lean CI, no-`sorry`, and theorem-catalog checks pass.

Analytic convergence, infinite-volume limits, and completed-space operator theory remain separate
later milestones.
