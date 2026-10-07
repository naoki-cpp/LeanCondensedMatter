# Low-order fermionic linked-cluster identities

The finite-mode fermionic Linked Cluster Theorem is available for every nonzero perturbation order.
The orders `1`, `2`, and `3` are also exposed explicitly because they make the factorial and
disconnected-subtraction conventions readable without unfolding the general moment-cumulant
machinery. These identities are an opt-in example/regression surface; the canonical linked-cluster
umbrella exports the general formal and analytic theorems instead.

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

The first identity fixes the normalization. The second displays cancellation of a partition into two
single-vertex components. The third displays both one-plus-two decompositions and the partition into
three singletons.

The generic power-series formulas live in
`Analysis/PowerSeries/LowOrderLog.lean`. The fermionic specializations live in
`SecondQuantization/Fermionic/Diagrammatics/LinkedCluster/LowOrder.lean`.

Connected-diagram statements at orders `1`, `2`, and `3` are obtained by specializing the
general fermionic linked-cluster theorem. Analytic low-order statements similarly follow by
combining the analytic/formal bridge

```text
(dⁿ/dλⁿ)|₀ log (Z(λ) / Z(0)) = n! [λⁿ] log Ẑ
```

with these formal identities, so separate public wrappers are not maintained.
