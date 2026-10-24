# Low-order fermionic linked-cluster identities

The finite-mode fermionic Linked Cluster Theorem is available for every nonzero perturbation order.
The orders `1`, `2`, and `3` make the factorial and disconnected-subtraction conventions readable
without unfolding the general moment-cumulant machinery. The explicit identities below are examples
of generic power-series theorems, not separate fermionic diagrammatic API declarations.

Write

```text
zₙ = [λⁿ] normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)).
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

The generic, kernel-checked formulas live in `Analysis/PowerSeries/LowOrderLog.lean`:
`Combinatorics.factorial_mul_coeff_logOf_one_eq`, `_two_eq`, and `_three_eq`.
They apply directly to the normalized fermionic `Common.dysonTraceSeries`, whose constant coefficient
is one by `PowerSeries.constantCoeff_normalizeByConstantCoeff` and
`Common.constantCoeff_dysonTraceSeries_ne_zero`. No specialized fermionic wrappers are maintained.

Connected-diagram statements at orders `1`, `2`, and `3` are obtained by specializing the
general fermionic linked-cluster theorem. Analytic low-order statements similarly follow by
combining the analytic/formal bridge

```text
(dⁿ/dλⁿ)|₀ log (Z(λ) / Z(0)) = n! [λⁿ] log Ẑ
```

with these formal identities, so separate public wrappers are not maintained.
