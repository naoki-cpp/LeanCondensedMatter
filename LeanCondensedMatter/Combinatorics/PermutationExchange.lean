import LeanCondensedMatter.Combinatorics.PermutationAssignmentCycleTrace
import LeanCondensedMatter.Combinatorics.PermutationCumulant

set_option linter.style.header false

/-!
# Exchange-weighted permutation backend

This is the canonical entry point for the project-local permutation theory.

The generic route is

```text
pairingSum ζ
  -- only the pairing/parity bridge requires ζ * ζ = 1
permutationSum ζ K S
  -- arbitrary ζ from here
singleCycleContribution ζ K S
  -- assignment-summed trace coefficients
PermutationCycleSeries
```

The imported modules keep the implementation layered:

* `PermutationConnectedDecomposition` owns the arbitrary-ζ permutation moment and its
  single-orbit contribution;
* `PermutationSingleCycleKernel`, `PermutationAssignmentCycleKernel`, and
  `PermutationAssignmentCycleTrace` derive the finite trace coefficients;
* `PermutationCumulant` exposes the actual Möbius-inversion consumer.

Callers should import this module for the complete permutation backend instead of depending on
its implementation layers individually. Determinant and permanent remain Mathlib/consumer
interpretations; they are not part of this generic entry point.
-/
