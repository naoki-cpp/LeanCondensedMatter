# Low-order fermionic linked-cluster identities

The finite-mode fermionic Linked Cluster Theorem is available for every nonzero perturbation order.
The orders `1`, `2`, and `3` make the factorial and disconnected-subtraction conventions readable
without unfolding the general moment-cumulant machinery. The explicit identities below are low-order consequences of the generic moment–cumulant
recurrence, not separate exported low-order or fermionic diagrammatic declarations.

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

The first-order identity is the kernel-checked `PowerSeries.coeff_one_logOf` in
`Analysis/PowerSeries/Normalization.lean`. The second- and third-order identities are
algebraic specializations of the kernel-checked
`Combinatorics.powerSeriesMomentCoeff_succ_recurrence` in
`Analysis/PowerSeries/Moment.lean`; the displayed equations are not
dedicated Lean theorem declarations. The recurrence applies to the normalized fermionic
`Common.dysonTraceSeries`, whose constant coefficient is one by
`PowerSeries.constantCoeff_normalizeByConstantCoeff` and
`Common.constantCoeff_dysonTraceSeries_ne_zero`.

Connected-diagram statements at orders `1`, `2`, and `3` are obtained by specializing the
general fermionic linked-cluster theorem. Analytic low-order statements similarly follow by
combining the analytic/formal bridge

```text
(dⁿ/dλⁿ)|₀ log (Z(λ) / Z(0)) = n! [λⁿ] log Ẑ
```

with these formal identities, so separate public wrappers are not maintained.
