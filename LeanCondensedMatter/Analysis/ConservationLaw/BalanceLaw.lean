import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Represented balance laws

This module packages a local balance law together with one chosen current extension

```text
J : OneForm → Obs
```

so that

```text
δ (Q f) = J (d f) + S f.
```

The representation-independent transport semantics belong to `IntrinsicBalanceLaw`.  `BalanceLaw`
is the explicit represented adapter: it remembers how the transport on exact differential data is
extended to all one-form-like inputs, and it owns operations that genuinely depend on that chosen
extension, including current/source shifts and current factorization.

The split into current and source is not generally unique. Over a ring of scalars, any linear
functional `K : OneForm → Obs` gives the equivalent decomposition

```text
J' = J + K,
S' = S - K ∘ d.
```

Thus the chosen full current contains representation data beyond the transport determined on
`range d`.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- A represented local balance law `δ(Q f) = J(d f) + S(f)`.

`current` is one chosen extension to all one-form-like data.  The balance equation constrains it
only on exact differential data `d f`; see `IntrinsicBalanceLaw` for the representation-independent
transport object.  The current/source split need not be unique; see `BalanceLaw.shiftCurrentSource`. -/
structure BalanceLaw
    (δ : Obs →ₗ[𝕜] Obs)
    (Q : Test →ₗ[𝕜] Obs)
    (d : Test →ₗ[𝕜] OneForm) where
  /-- Chosen flux/current functional on all one-form-like data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Local source, sink, or torque functional. -/
  source : Test →ₗ[𝕜] Obs
  /-- The represented local balance identity. -/
  balance : ∀ f, δ (Q f) = current (d f) + source f

namespace BalanceLaw

/-- A source-free represented balance law supplies a differential current representation of the
full localized evolution `δ ∘ Q`. -/
def toDifferentialCurrentRepresentation
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) (hsource : B.source = 0) :
    DifferentialCurrentRepresentation d (δ.comp Q) where
  current := B.current
  factors := by
    intro f
    have h := B.balance f
    rw [hsource] at h
    simpa using h

section CurrentSourceAmbiguity

variable {R Test' OneForm' Obs' : Type*}
variable [CommRing R]
variable [AddCommMonoid Test'] [Module R Test']
variable [AddCommMonoid OneForm'] [Module R OneForm']
variable [AddCommMonoid Obs'] [Module R Obs']

/-- Shift an arbitrary differential functional from the source into the current without changing
what the balance law says.

For `K : OneForm' → Obs'`, this realizes

```text
J' = J + K,
S' = S - K ∘ d.
```

The subtraction is written as scalar multiplication by `-1`, so the construction only needs the
module structure on observables. -/
noncomputable def shiftCurrentSource
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (K : OneForm' →ₗ[R] Obs') :
    BalanceLaw δ Q d where
  current := B.current + K
  source := B.source + (-1 : R) • K.comp d
  balance := by
    intro f
    rw [B.balance f]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    module

@[simp]
theorem shiftCurrentSource_current
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (K : OneForm' →ₗ[R] Obs') :
    (B.shiftCurrentSource K).current = B.current + K :=
  rfl

@[simp]
theorem shiftCurrentSource_source
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (K : OneForm' →ₗ[R] Obs') :
    (B.shiftCurrentSource K).source = B.source + (-1 : R) • K.comp d :=
  rfl

/-- The current/source shift leaves the total right-hand side of the balance equation unchanged. -/
theorem shiftCurrentSource_total
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (K : OneForm' →ₗ[R] Obs') (f : Test') :
    (B.shiftCurrentSource K).current (d f) + (B.shiftCurrentSource K).source f =
      B.current (d f) + B.source f := by
  change (B.current + K) (d f) +
      (B.source + (-1 : R) • K.comp d) f = B.current (d f) + B.source f
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  module

/-- If the source itself factors through the differential, it can be absorbed completely into the
current. The resulting current is `B.current + sourceCurrent` and represents the full localized
evolution `δ ∘ Q` with no remaining source term. -/
noncomputable def toDifferentialCurrentRepresentationOfSourceFactors
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (sourceCurrent : OneForm' →ₗ[R] Obs')
    (hsource : IsDifferentialCurrent d B.source sourceCurrent) :
    DifferentialCurrentRepresentation d (δ.comp Q) :=
  (B.shiftCurrentSource sourceCurrent).toDifferentialCurrentRepresentation (by
    apply LinearMap.ext
    intro f
    change B.source f + (-1 : R) • sourceCurrent (d f) = 0
    rw [hsource f]
    module)

@[simp]
theorem toDifferentialCurrentRepresentationOfSourceFactors_current
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (sourceCurrent : OneForm' →ₗ[R] Obs')
    (hsource : IsDifferentialCurrent d B.source sourceCurrent) :
    (B.toDifferentialCurrentRepresentationOfSourceFactors sourceCurrent hsource).current =
      B.current + sourceCurrent :=
  rfl

end CurrentSourceAmbiguity

end BalanceLaw

end ConservationLaw
