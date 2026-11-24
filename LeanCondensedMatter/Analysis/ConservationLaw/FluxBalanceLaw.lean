import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Flux balance laws independent of the choice of current

This module is the semantic owner of local balance identities without a chosen current extension. It
separates the transport content of a local balance law from a chosen extension of that transport to
all one-form-like test data.

For

```text
d : Test → OneForm
Q : Test → Obs
δ : Obs → Obs
```

the differential-dependent transport/flux is a linear functional

```text
Φ : Test → Obs
```

that depends only on `d f`.  A local balance law is then

```text
δ (Q f) = Φ f + S f.
```

A full current functional `J : OneForm → Obs` is downstream representation data satisfying
`Φ f = J (d f)`.  This distinction matters because the balance equation determines only the flux
on exact differential data; an extension of that flux away from `range d` need not be unique.

A chosen full current is supplied independently by `DifferentialCurrentRepresentation d Φ`;
no second balance-law structure is needed. `FluxBalanceLaw` records the representation-independent
transport and source split and owns the generic evolution, source-free, uniqueness, scaling,
and current/source redistribution results.

The word *flux* describes a term in the balance equation, not an intrinsic
(Berry-curvature or disorder-independent) transport mechanism.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- Representation-independent local balance data.

`transport` is defined on test objects themselves and is required only to depend on their
differentials.  A full `OneForm → Obs` current is deliberately not part of this structure. -/
structure FluxBalanceLaw
    (δ : Obs →ₗ[𝕜] Obs)
    (Q : Test →ₗ[𝕜] Obs)
    (d : Test →ₗ[𝕜] OneForm) where
  /-- Flux defined on test data, without choosing a full one-form current. -/
  transport : Test →ₗ[𝕜] Obs
  /-- Transport is insensitive to changes of a test object that leave its differential fixed. -/
  transport_depends : Function.FactorsThrough transport d
  /-- Local source, sink, or torque functional. -/
  source : Test →ₗ[𝕜] Obs
  /-- The local balance identity. -/
  balance : ∀ f, δ (Q f) = transport f + source f

namespace FluxBalanceLaw

/-- Representation-independent transport vanishes on test objects annihilated by the differential. -/
theorem transport_eq_zero_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    B.transport f = 0 :=
  calc
    B.transport f = B.transport 0 :=
      B.transport_depends (by simpa only [map_zero] using hf)
    _ = 0 := map_zero B.transport

/-- If the differential test vanishes, only the source can change the localized quantity. -/
theorem evolution_eq_source_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    δ (Q f) = B.source f := by
  rw [B.balance f, B.transport_eq_zero_of_differential_eq_zero hf, zero_add]

/-- A test object in the kernel of `d` gives a conserved quantity when its source also vanishes. -/
theorem evolution_eq_zero_of_differential_eq_zero_of_source_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) {f : Test}
    (hf : d f = 0) (hsource : B.source f = 0) :
    δ (Q f) = 0 := by
  rw [B.evolution_eq_source_of_differential_eq_zero hf, hsource]

/-- In a source-free law, transport flux is exactly the localized evolution. -/
theorem sourceFreeFlux_eq_evolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) (hsource : B.source = 0) (f : Test) :
    B.transport f = δ (Q f) := by
  have h := B.balance f
  rw [hsource] at h
  simpa using h.symm

/-- Source-free transport flux is unique for fixed evolution, localized quantity, and differential. -/
theorem sourceFreeFlux_unique
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B₁ B₂ : FluxBalanceLaw δ Q d)
    (hsource₁ : B₁.source = 0) (hsource₂ : B₂.source = 0) (f : Test) :
    B₁.transport f = B₂.transport f := by
  calc
    B₁.transport f = δ (Q f) := B₁.sourceFreeFlux_eq_evolution hsource₁ f
    _ = B₂.transport f := (B₂.sourceFreeFlux_eq_evolution hsource₂ f).symm

/-- Scaling the evolution scales representation-independent transport and source. -/
noncomputable def scaleEvolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d) (c : 𝕜) :
    FluxBalanceLaw (c • δ) Q d where
  transport := c • B.transport
  transport_depends := by
    intro f g hfg
    simpa only [LinearMap.smul_apply] using
      congrArg (fun y : Obs => c • y) (B.transport_depends hfg)
  source := c • B.source
  balance := by
    intro f
    simp only [LinearMap.smul_apply]
    rw [B.balance f]
    exact smul_add c (B.transport f) (B.source f)

section TransportSourceAmbiguity

variable {R T F O : Type*} [CommRing R]
variable [AddCommMonoid T] [Module R T]
variable [AddCommMonoid F] [Module R F]
variable [AddCommMonoid O] [Module R O]

/-- Redistribute a differential-dependent functional from source to transport without changing
the localized evolution. A shift of a full current by `J` is the special case
`K = J.comp d`; no full current extension is required. -/
noncomputable def shiftTransportSource
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) : FluxBalanceLaw δ Q d where
  transport := B.transport + K
  transport_depends := by
    intro f g hfg
    simp only [LinearMap.add_apply]
    rw [B.transport_depends hfg, hK hfg]
  source := B.source + (-1 : R) • K
  balance := by
    intro f
    rw [B.balance f]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    module

@[simp]
theorem shiftTransportSource_transport
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) :
    (B.shiftTransportSource K hK).transport = B.transport + K :=
  rfl

@[simp]
theorem shiftTransportSource_source
    {δ : O →ₗ[R] O} {Q : T →ₗ[R] O} {d : T →ₗ[R] F}
    (B : FluxBalanceLaw δ Q d) (K : T →ₗ[R] O)
    (hK : Function.FactorsThrough K d) :
    (B.shiftTransportSource K hK).source = B.source + (-1 : R) • K :=
  rfl

end TransportSourceAmbiguity

/-- If the source itself depends only on differential data, it may be absorbed into transport.
The resulting law is source-free without choosing any full current functional. -/
noncomputable def absorbSource
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d)
    (hsource : Function.FactorsThrough B.source d) :
    FluxBalanceLaw δ Q d where
  transport := B.transport + B.source
  transport_depends := by
    intro f g hfg
    simp only [LinearMap.add_apply]
    rw [B.transport_depends hfg, hsource hfg]
  source := 0
  balance := by
    intro f
    rw [B.balance f]
    simp

end FluxBalanceLaw

end ConservationLaw
