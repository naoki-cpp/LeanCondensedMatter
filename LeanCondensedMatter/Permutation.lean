import LeanCondensedMatter.Permutation.PairingBridge
import LeanCondensedMatter.Permutation.Cumulant
import LeanCondensedMatter.Permutation.TraceLog
import LeanCondensedMatter.Permutation.GrandPartitionSeries

set_option linter.style.header false

/-!
# Weighted permutation theory

This is the canonical interface for the project's `ζ`-weighted permutation theory.

```text
pairingSum ζ
  -- only this parity bridge requires ζ * ζ = 1
permutationSum ζ K S
  -- arbitrary ζ from here
singleCycleContribution ζ K S
  → ζ^(m - 1) * tr(K^m) / m
  → permutationConnectedCycleSeries ζ K
  → formal trace-log identity
  → permutationGrandPartitionSeries ζ K
  → logOf grand series = connected-cycle series
```

The implementation uses the generic finite-partition, cumulant, perfect-pairing, matrix, and power
series machinery owned by `Combinatorics`, Mathlib, and `Analysis`, but the complete weighted
permutation route is local to this module.

On a full finite matrix index type, the weight `ζ ^ cycleDefect σ` is the standard
alpha-determinant weight. No project-local determinant, permanent, or alpha-determinant alias is
introduced: determinant and permanent remain consumer-side interpretations at `ζ = -1` and
`ζ = 1`.
-/
