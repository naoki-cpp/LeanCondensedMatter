import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Abstract balance laws

This module isolates the representation-independent content of a local balance law. A smeared or
localized quantity

```text
Q : Test → Obs
```

with evolution `δ : Obs → Obs` satisfies a balance law when its evolution splits into a transport
term depending only on differential test data and a source term:

```text
δ (Q f) = J (d f) + S f.
```

No Hamiltonian, localization operator, velocity, current-density formula, continuum model, or
particle statistics is assumed here.

The split into current and source is not generally unique. Over a ring of scalars, any linear
functional `K : OneForm → Obs` gives the equivalent decomposition

```text
J' = J + K,
S' = S - K ∘ d.
```

Thus only the total `J (d f) + S f` is fixed by the balance equation until additional physical or
geometric conditions select a particular current/source split.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- A local balance law `δ(Q f) = J(d f) + S(f)`.

`current` represents transport through differential-like test data, while `source` contains the
part of the local evolution assigned to local production, loss, or torque. This split need not be
unique; see `BalanceLaw.shiftCurrentSource`. -/
structure BalanceLaw
    (δ : Obs →ₗ[𝕜] Obs)
    (Q : Test →ₗ[𝕜] Obs)
    (d : Test →ₗ[𝕜] OneForm) where
  /-- Flux/current functional acting on differential-like test data. -/
  current : OneForm →ₗ[𝕜] Obs
  /-- Local source, sink, or torque functional. -/
  source : Test →ₗ[𝕜] Obs
  /-- The local balance identity. -/
  balance : ∀ f, δ (Q f) = current (d f) + source f

namespace BalanceLaw

/-- Evaluate a balance law on one test object. -/
theorem apply
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) (f : Test) :
    δ (Q f) = B.current (d f) + B.source f :=
  B.balance f

/-- If the differential test vanishes, only the source term can change the localized quantity. -/
theorem evolution_eq_source_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    δ (Q f) = B.source f := by
  rw [B.balance f, hf, map_zero, zero_add]

/-- A test object in the kernel of `d` gives a conserved quantity when its source also vanishes. -/
theorem evolution_eq_zero_of_differential_eq_zero_of_source_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) {f : Test}
    (hf : d f = 0) (hsource : B.source f = 0) :
    δ (Q f) = 0 := by
  rw [B.evolution_eq_source_of_differential_eq_zero hf, hsource]

/-- Scaling the evolution scales both transport and source while preserving the same localized
quantity and differential. -/
noncomputable def scaleEvolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) (c : 𝕜) :
    BalanceLaw (c • δ) Q d where
  current := c • B.current
  source := c • B.source
  balance := by
    intro f
    simp only [LinearMap.smul_apply]
    rw [B.balance f]
    exact smul_add c (B.current (d f)) (B.source f)

/-- A source-free balance law is a differential current representation of the full localized
evolution `δ ∘ Q`. -/
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
noncomputable def toDifferentialCurrentRepresentation_of_source_factors
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (sourceCurrent : OneForm' →ₗ[R] Obs')
    (hsource : FactorsThroughDifferential d B.source sourceCurrent) :
    DifferentialCurrentRepresentation d (δ.comp Q) :=
  (B.shiftCurrentSource sourceCurrent).toDifferentialCurrentRepresentation (by
    apply LinearMap.ext
    intro f
    change B.source f + (-1 : R) • sourceCurrent (d f) = 0
    rw [hsource f]
    module)

@[simp]
theorem toDifferentialCurrentRepresentation_of_source_factors_current
    {δ : Obs' →ₗ[R] Obs'}
    {Q : Test' →ₗ[R] Obs'}
    {d : Test' →ₗ[R] OneForm'}
    (B : BalanceLaw δ Q d)
    (sourceCurrent : OneForm' →ₗ[R] Obs')
    (hsource : FactorsThroughDifferential d B.source sourceCurrent) :
    (B.toDifferentialCurrentRepresentation_of_source_factors sourceCurrent hsource).current =
      B.current + sourceCurrent :=
  rfl

end CurrentSourceAmbiguity

end BalanceLaw

end ConservationLaw
