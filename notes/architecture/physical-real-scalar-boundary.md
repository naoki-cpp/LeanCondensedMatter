# Physical real scalar boundary

This document defines how QuantumTheory code may transport complex expressions into real-valued
physical APIs. It complements the density-state architecture and is enforced by
`scripts/check_quantum_physical_scalar_boundary.py`.

## Three distinct operations

### 1. Arbitrary real-part projection

A public physical quantity must not be defined by taking the real part of an otherwise arbitrary
complex expression:

```lean
noncomputable def badExpectation (z : ℂ) : ℝ := z.re
```

The type `ℝ` alone does not prove that the discarded imaginary component was zero. Such a definition
can silently hide an orientation error, a missing self-adjointness hypothesis, or a genuinely
complex response function.

### 2. Lossless transport after a reality proof

When the mathematics proves that a complex scalar is real, the preferred API stores that proof and
then transports the scalar without loss. Existing examples include:

```lean
Complex.selfAdjointEquiv
ContinuousLinearMap.diagonalExpectationValue
QuantumTheory.observableExpValue
DensityOperator.observableExpectation
```

Nonnegativity should likewise be represented in the codomain when available, as in
`probNNReal : NNReal`. A compatibility `ℝ` API may be a direct coercion from the stronger type.

### 3. Proof-only extraction of a real equality

Proofs may apply `Complex.re`, `.re`, or `Complex.reCLM` to an equality whose complex meaning has
already been established. For example, extracting real components can transport a proved complex
series identity into an `ℝ` theorem. This is a proof technique; it does not define the physical
quantity.

The audit therefore examines public definition bodies and deliberately ignores theorem and lemma
bodies.

## Automated audit

The physical scalar boundary audit scans `LeanCondensedMatter/QuantumTheory/**/*.lean` and rejects a
public `def` or `abbrev` when all of the following hold:

- its explicitly declared result is `ℝ`, `Real`, `NNReal`, `ENNReal`, `ℝ≥0`, or `ℝ≥0∞`, including a
  function type ending in one of those scalars;
- its definition body contains direct `.re` or `Complex.re` projection;
- the declaration is not `private`;
- no declaration-specific allowlist entry exists.

Both ordinary `:=` definitions and equation-style definitions are recognized. Complex-valued
functions, theorem bodies, and private implementation helpers are outside this public API guard.

## Allowlist policy

The allowlist is intentionally declaration-specific. Each entry consists of an exact repository
path, an exact declaration name, and a nonempty mathematical rationale. Directory-wide exemptions
are not supported. CI rejects stale entries that no longer correspond to a detected projection.

The default and current allowlist is empty. Introducing an entry should be treated as temporary
technical debt unless the projection itself is part of the intended mathematical object rather than
a claim that a complex quantity is physically real.

## Review rule

For every new real-valued physical API, reviewers should ask which of the following justifies its
codomain:

1. the source expression is intrinsically real by construction;
2. a self-adjointness or reality proof supports lossless transport;
3. a stronger ordered type such as `NNReal` or `ENNReal` captures the physical invariant directly.

If none applies, the public API should remain complex-valued rather than discard information.
