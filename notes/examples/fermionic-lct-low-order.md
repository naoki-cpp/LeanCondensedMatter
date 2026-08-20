# Low-order fermionic linked-cluster identities

The finite-mode fermionic Linked Cluster Theorem is available for every nonzero perturbation order.
The orders `1`, `2`, and `3` are also exposed as explicit regression corollaries because they make
the factorial and disconnected-subtraction conventions readable without unfolding the general
moment-cumulant machinery.

Write

```text
zₙ = normalizedDysonPartitionCoeff ε β (quarticInteraction g) n.
```

The formal logarithm satisfies

```text
1! [λ]  log Z = z₁,
2! [λ²] log Z = 2 z₂ - z₁²,
3! [λ³] log Z = 6 z₃ - 6 z₁ z₂ + 2 z₁³.
```

The first identity fixes the normalization. The second checks cancellation of a partition into two
single-vertex components. The third checks both one-plus-two decompositions and the partition into
three singletons. Each polynomial is proved equal to the sum of amplitudes over connected quartic
Wick diagrams on `Fin 1`, `Fin 2`, or `Fin 3`.

The generic power-series formulas live in
`Analysis/PowerSeries/LowOrderLog.lean`. The fermionic formal corollaries live in
`SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/LowOrder.lean`, and the analytic
logarithmic-derivative corollaries live in
`SecondQuantization/Fermionic/Perturbation/AnalyticLinkedClusterLowOrder.lean`.

The analytic statements use the same right-hand sides because

```text
(dⁿ/dλⁿ)|₀ log (Z(λ) / Z(0)) = n! [λⁿ] log Ẑ
```

is already proved by the analytic/formal bridge. Thus these corollaries test the formal logarithm,
the analytic derivative convention, and the connected-diagram theorem with one shared factorial and
sign normalization.
