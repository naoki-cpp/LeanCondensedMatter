# Roadmap — Fermionic Linked Cluster Theorem

This page is the execution plan for the finite-mode, finite-temperature fermionic Linked Cluster
Theorem (LCT). It complements the longer historical narrative in
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

The left side is the exponential-generating normalization of a coefficient of the normalized formal
Dyson `log Z`. The right side is the sum of amplitudes of connected quartic Wick diagrams on the
labelled vertex set `Finset.univ : Finset (Fin n)`.

## Completed foundation

The following load-bearing pieces are already proved and compile without `sorry`.

### Dyson and Wick expansion

- `Fermionic/Perturbation/DysonExpansion.lean` defines the genuine iterated-integral coefficients
  `dysonCoeff`.
- `Fermionic/Perturbation/DysonPartitionSeries.lean` packages their thermal traces into
  `dysonPartitionSeries` and defines `dysonFormalLogPartitionFunction`.
- `Fermionic/Perturbation/DysonVertexMoment.lean` converts ordinary power-series coefficients into
  finite-set moments with the required factorial normalization.
- `Fermionic/Diagrammatics/DysonDiagramExpansion.lean` proves

  ```lean
  dysonVertexMoment ε β (quarticInteraction g) S =
    ∑ d : QuarticWickDiagram Mode N S,
      quarticWickDiagramAmplitude ε β g d
  ```

### Diagram connectedness

- Quartic Wick diagrams have a component partition, connected restrictions, reassembly, and a
  component-decomposition equivalence.
- `Combinatorics/DiagramConnectedness.lean` proves the abstract theorem that the cumulant of a
  factorizing weighted diagram family is the sum of connected-diagram weights.
- Coupling products and the Dyson sign already factor over connected components in
  `WickDiagram/AmplitudePrefactorFactorization.lean`.

### Ordered-simplex shuffle calculus

The analytic binary-shuffle layer is complete.

- `Analysis/OrderedSimplexIntegralCalculus.lean` proves the product recurrence for two
  ordered-simplex integrals.
- `Combinatorics/BinaryShuffle.lean` defines finite order-preserving binary shuffles and their outer
  left/right decomposition.
- `Analysis/BinaryShuffleOrderedSimplex.lean` proves that the finite sum of explicit binary-shuffle
  contributions equals the product of the two component ordered-simplex integrals.
- `Combinatorics/BinaryShuffleSlots.lean` turns each recursive shuffle into an order-preserving
  equivalence

  ```lean
  Fin m ⊕ Fin n ≃ Fin (m + n)
  ```

- Global vertex orders already decompose into component-local orders and a
  `QuarticDiagram.ComponentShuffle`.
- `Common/Diagrammatics/ComponentOrderedSimplex.lean` defines component-restricted time assignments,
  shuffled products of component integrands, continuity, and finite-sum/integral interchange.

The binary shuffle sequence was completed by PRs #237–#241. Component-order and component-shuffle
infrastructure was completed immediately before it in PRs #233–#235.

## Remaining critical path

### 1. Identify binary shuffles with two-family slot shuffles

`BinaryShuffle.toSlotShuffle` currently forgets the recursive presentation. Prove that this map is an
equivalence, or provide an equivalent canonical inverse from an order-preserving slot equivalence.

Expected output:

```lean
BinaryShuffle m n ≃ BinaryShuffle.SlotShuffle m n
```

This supplies the uniqueness needed to reindex finite sums, rather than only constructing one ambient
slot equivalence from each recursive shuffle.

### 2. Prove the finite-family component-shuffle product identity

Transport the binary formula to two component blocks, then iterate it across the finite type
`d.componentPartition.parts`.

Expected theorem shape:

```lean
∑ shuffle : d.ComponentShuffle,
    orderedSimplexIntegral S.card β
      (d.componentShuffleIntegrand shuffle componentIntegrand)
  =
  ∏ B : d.componentPartition.parts,
    orderedSimplexIntegral (B : Finset (Fin N)).card β (componentIntegrand B)
```

This stage is statistics-independent and should live in `Common/Diagrammatics` or in a general
`Analysis`/`Combinatorics` layer with a Common specialization.

### 3. Factor the fermionic contraction integrand

For an assembled global order, prove that the Wick contraction integrand is the product of the
connected-component contraction integrands evaluated on component-restricted times.

Expected theorem shape:

```lean
d.contractionIntegrand ε β (d.assembleVertexOrder orders shuffle) τ =
  ∏ B : d.componentPartition.parts,
    ((d.restrictComponentConnected B.2).1.contractionIntegrand
      ε β (orders B) (d.componentTimeAssignment shuffle τ B))
```

This requires four compatibility results:

1. the transported global pairing decomposes into the pairings of the component restrictions;
2. each global pair value agrees with the corresponding restricted pair value;
3. the product over global pairs reindexes to the product over components and local pairs;
4. the fermionic pairing weight factors over components.

The fourth item is the main proof risk. `Pairing.weight` is not invariant under an arbitrary relabeling.
The proof must use the special block-of-four vertex-leg permutation induced by a component shuffle and
show that its cross-component parity contribution is even.

### 4. Prove complete amplitude factorization

Combine the component-shuffle product theorem, contraction-integrand factorization, and the already
proved scalar-prefactor factorization.

Expected theorem:

```lean
quarticWickDiagramAmplitude ε β g d =
  ∏ B : d.componentPartition.parts,
    quarticWickDiagramAmplitude ε β g
      ((d.restrictComponentConnected B.2).1)
```

### 5. Instantiate `WeightedDiagramFamily`

Use

```lean
Diagram S          := QuarticWickDiagram Mode N S
ConnectedDiagram S := ConnectedQuarticWickDiagram Mode N S
diagramWeight       := quarticWickDiagramAmplitude ε β g
connectedWeight     := quarticWickDiagramAmplitude ε β g
```

with the existing component-decomposition equivalence and the amplitude-factorization theorem. The
abstract diagram-connectedness theorem and Dyson diagram expansion should then yield

```lean
dysonVertexCumulant ε β (quarticInteraction g) S =
  ∑ d : ConnectedQuarticWickDiagram Mode N S,
    quarticWickDiagramAmplitude ε β g d
```

for nonempty `S`.

### 6. Connect finite-set cumulants to coefficients of formal `log Z`

Prove the exponential-generating-series bridge for an arbitrary normalized power series. The desired
general theorem has the shape

```lean
(n.factorial : ℂ) * PowerSeries.coeff n (formalLogPartitionFunction Z) =
  Finpartition.cumulantFromMoment
    (fun S => (S.card.factorial : ℂ) * PowerSeries.coeff S.card Z)
    Finset.univ
```

under `PowerSeries.constantCoeff Z = 1` and `n ≠ 0`.

This is the second main proof risk. It must align Mathlib's ordinary power-series multiplication with
labelled set partitions and their multinomial factors. The proof should be general and independent of
second quantization.

### 7. Final Dyson specialization

Specialize the EGF/log theorem to

```lean
normalizePartitionSeries (dysonPartitionSeries ε β (quarticInteraction g))
```

identify its finite-set moment with `dysonVertexMoment`, and compose with stage 5. This final PR should
contain little new combinatorics; it should mainly rewrite and combine previously proved theorems.

## Suggested PR sequence

The expected remaining implementation is approximately seven to ten focused PRs:

1. `BinaryShuffle ≃ SlotShuffle` and sum reindexing;
2. two-component `ComponentShuffle` transport;
3. arbitrary finite-family component-shuffle product identity;
4. pairing restriction and pair-value compatibility;
5. fermionic pairing-sign factorization;
6. full contraction-integrand and amplitude factorization;
7. concrete `WeightedDiagramFamily` and finite-set connected-diagram theorem;
8. general finite-set cumulant/formal-log EGF bridge, possibly split into two PRs;
9. final Dyson LCT specialization.

The sequence can be compressed when adjacent statements elaborate cleanly, but pairing-sign and EGF
work should remain isolated because they are the highest-risk proofs.

## Definition of done

The algebraic fermionic LCT milestone is complete when:

- the target theorem above is exported by the Fermionic API;
- it assumes finite `Mode`, the existing ordering/typeclass hypotheses, and `n ≠ 0`, but no analytic
  convergence of the perturbation series;
- all intermediate theorems compile without `sorry`;
- the result uses the existing `quarticWickDiagramAmplitude` without changing its sign or factorial
  conventions;
- repository-wide Lean CI, no-`sorry`, and theorem-catalog checks pass.

Analytic convergence, infinite-volume limits, and completed-space operator theory remain separate later
milestones.