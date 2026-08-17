import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation

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
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- A local balance law `δ(Q f) = J(d f) + S(f)`.

`current` represents transport through differential-like test data, while `source` contains the
part of the local evolution that remains even when the differential test vanishes. -/
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

end BalanceLaw

end ConservationLaw
