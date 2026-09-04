# Physical real scalar boundary

This document defines how QuantumTheory code transports complex expressions into real-valued
physical APIs. It complements the density-state architecture. CI protects the source architecture,
build, lints, and kernel-level correctness checks; `scripts/CheckArchitecture.lean` remains available
as a focused local audit of compiled semantic relationships without prescribing proof bodies.

## Three distinct operations

### 1. Arbitrary real-part projection

A public physical quantity should not be justified merely by taking the real part of an otherwise
arbitrary complex expression:

```lean
noncomputable def badExpectation (z : ℂ) : ℝ := z.re
```

The type `ℝ` alone does not prove that the discarded imaginary component was zero. Such a definition
can hide an orientation error, a missing self-adjointness hypothesis, or a genuinely complex
response function. The mathematical API should expose why the scalar is real rather than make a
projection stand in for that proof.

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
needed again. Equality of real scalars can often be proved by coercing them to `ℂ` and applying
`Complex.ofReal_injective` rather than by projecting both sides with `.re`.

Nonnegativity should likewise be represented in the codomain when available, as in
`diagonalExpectationNNReal` and `probNNReal : NNReal`. A compatibility `ℝ` API may be a direct
coercion from the stronger type.

### 3. Proof-level transport and genuine components

`Complex.re` and `.re` remain appropriate when the real component itself is the mathematical
quantity, or when a proof genuinely reasons about real and imaginary components. What should be
avoided is using a projection merely to transport an equality or convergent series that is already
known to consist of real scalars.

In particular, a `HasSum` over complex coercions of real terms can be transported back to `ℝ`
losslessly, for example with `exact_mod_cast`. Conversely, a real `HasSum` may be embedded into `ℂ`
through `Complex.ofRealCLM` when a complex equality is the natural target.

## Compiled architecture audit

The optional compiled audit inspects the stable typed bridge rather than the text of its
implementation. It can check canonical ownership and semantic relationships for endpoints including:

- `QuantumTheory.expValueSelfAdjoint` and `QuantumTheory.coe_observableExpValue`;
- `DensityOperator.observableExpectationSelfAdjoint` and `DensityOperator.expectation_observable`;
- `QuantumTheory.probSelfAdjoint`, `DensityOperator.expectation_effect_eq_probNNReal`, and
  `QuantumTheory.hasSum_probNNReal`;
- `QuantumTheory.bornPMF_apply` as the typed probability bridge.

For selected bridge theorems, the compiled declaration type can be checked to mention the canonical
complex and real/nonnegative APIs it relates. Declaration ownership is resolved through the Lean
environment, not by recognizing `def`/`theorem` syntax in source text. These checks are useful when
reviewing a focused architecture refactor, but are not permanent pull-request regression guards.

This deliberately does **not** make `.re`, `Complex.re`, `Complex.reCLM`, `exact_mod_cast`, or any
other proof helper into a CI token rule. Proofs are free to change as long as the mathematical API
remains valid. If a future API needs a stronger invariant, prefer a theorem or type-level contract
that expresses the mathematics directly.

## Review rule

For every new real-valued physical API, reviewers should ask which of the following justifies its
codomain:

1. the source expression is intrinsically real by construction;
2. a self-adjointness or reality proof supports lossless transport;
3. a stronger ordered type such as `NNReal` or `ENNReal` captures the physical invariant directly.

If none applies, the public API should remain complex-valued rather than discard information.

Durable guarantees should live in the Lean API or in structural source architecture checks. Use the
compiled audit as a focused refactor tool rather than freezing one declaration layout as CI policy.
