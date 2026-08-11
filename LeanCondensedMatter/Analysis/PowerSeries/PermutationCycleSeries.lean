import LeanCondensedMatter.Analysis.PowerSeries.PermutationTraceLog

set_option linter.style.header false

/-!
# Exchange-weighted permutation cycle series

This is the canonical entry point for the W3 generating-series layer. The implementation remains
split by proof dependency, but the public story is one route:

```text
permutationSum ζ
  → singleCycleContribution ζ
  → ζ^(m - 1) * tr(K^m) / m
  → permutationConnectedCycleSeries ζ K
  → formal trace-log identity
```

The `ζ = 0` coefficientwise boundary is owned by the connected-cycle-series layer. The
formal trace-log identity and the diagonal-kernel theorem are owned by
`PermutationTraceLog`.

This module deliberately contains no determinant or permanent specialization. Those are
consumer-side interpretations; in particular, the finite fermionic statement
`Z₀ = det (1 + K)` remains in the fermionic thermal consumer.

Callers should import this module for the complete generic permutation-cycle series API rather than
depending on `PermutationCycleEGF`, `PermutationConnectedCycleSeries`, and
`PermutationTraceLog` separately.
-/
