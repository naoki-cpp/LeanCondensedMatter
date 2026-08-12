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
complex response function. Using `Complex.reCLM` in a public real-valued definition has the same
information-discarding semantics and is governed by the same rule.

### 2. Lossless transport after a reality proof

When the mathematics proves that a complex scalar is real, the preferred API stores that proof and
then transports the scalar without loss. Existing examples include:

```lean
Complex.selfAdjointEquiv
ContinuousLinearMap.diagonalExpectationValue
ContinuousLinearMap.diagonalExpectationNNReal
QuantumTheory.observableExpValue
DensityOperator.observableExpectation
```

For a proved-real scalar `z`, package `z` as `selfAdjoint ℂ`, use `Complex.selfAdjointEquiv` to obtain
the corresponding `ℝ`, and use `Complex.coe_selfAdjointEquiv` when the original complex scalar is
needed again. Equality of real scalars should usually be proved by coercing them to `ℂ` and applying
`Complex.ofReal_injective` rather than by projecting both sides with `.re`.

Nonnegativity should likewise be represented in the codomain when available, as in
`diagonalExpectationNNReal` and `probNNReal : NNReal`. A compatibility `ℝ` API may be a direct
coercion from the stronger type.

### 3. Proof-level transport and genuine components

`Complex.re` and `.re` remain appropriate when the real component itself is the mathematical
quantity, or when a proof genuinely reasons about real and imaginary components. What should be
avoided is using a projection merely to transport an equality or convergent series that is already
known to consist of real scalars.

In particular, a `HasSum` over complex coercions of real terms should be transported back to `ℝ`
losslessly, for example with `exact_mod_cast`, rather than by applying `Complex.reCLM`. Conversely,
a real `HasSum` may be embedded into `ℂ` through `Complex.ofRealCLM` when a complex equality is the
natural target.

The audit therefore continues to allow theorem-local `.re` where it represents a genuine component,
but rejects `Complex.reCLM` throughout `QuantumTheory` because that pattern is almost always a
lossy transport of an already-real series identity.

## Automated audit

The physical scalar boundary audit scans `LeanCondensedMatter/QuantumTheory/**/*.lean` and rejects a
public `def`, `abbrev`, or `opaque` declaration when all of the following hold:

- its explicitly declared result is `ℝ`, `Real`, `NNReal`, `ENNReal`, `ℝ≥0`, or `ℝ≥0∞`, including a
  function type ending in one of those scalars;
- its definition body contains direct `.re`, `Complex.re`, or `Complex.reCLM` projection;
- the declaration is neither `private` nor `local`;
- no declaration-specific allowlist entry exists.

In addition, any use of `Complex.reCLM` inside `QuantumTheory` is rejected, including theorem and
lemma bodies. Use a proved-real scalar plus coercion / injectivity instead.

Both ordinary `:=` definitions and equation-style definitions are recognized, including declarations
with attributes such as `@[simp]`. Complex-valued functions and private or local implementation
helpers remain outside the public-definition guard; the separate `reCLM` rule still applies to all
QuantumTheory Lean files.

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
