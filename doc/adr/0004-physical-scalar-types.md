---
status: accepted
---

# Preserve reality and positivity at physical scalar boundaries

A physical quantity that is mathematically real should expose the proof of reality before being transported from complex scalars. Use the self-adjoint scalar equivalence for lossless conversion, stronger nonnegative types for probabilities, and extended nonnegative reals for entropy that may diverge.

Taking an arbitrary complex expression's real part would silently discard information and could hide a missing self-adjointness hypothesis. The stronger boundary costs additional proof work but lets downstream users rely on reality or positivity and recover the original complex value exactly. Real-part projection remains appropriate when the real component itself is the intended quantity.

The canonical APIs include real observable expectations, `probNNReal` and `bornPMF` for discrete measurements, and `vonNeumannEntropy : ENNReal`. Their codomains express different guarantees; finite entropy requires a separate finiteness result.

Evidence: [physical scalar policy](../../notes/architecture/physical-real-scalar-boundary.md), [observable definitions](../../LeanCondensedMatter/QuantumTheory/Postulates.lean), [entropy definition](../../LeanCondensedMatter/QuantumTheory/Entropy/Basic.lean), and [measurement architecture](../../notes/architecture/quantum-density-theory.md).
