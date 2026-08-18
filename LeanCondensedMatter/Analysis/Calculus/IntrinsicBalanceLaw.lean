import LeanCondensedMatter.Analysis.Calculus.BalanceLaw
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Intrinsic transport balance laws

This module separates the transport content of a local balance law from a chosen extension of that
transport to all one-form-like test data.

For

```text
d : Test → OneForm
Q : Test → Obs
δ : Obs → Obs
```

the intrinsic transport object is a linear functional

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

`ConservationLaw.BalanceLaw` is retained as the represented form carrying such a chosen `J`.
`IntrinsicBalanceLaw` records only the representation-independent transport and source split.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- A transport functional depends only on differential data when equal differentials give equal
transport.  This is weaker than choosing an extension `J : OneForm → Obs`. -/
def DependsOnlyOnDifferential
    (d : Test →ₗ[𝕜] OneForm) (Φ : Test →ₗ[𝕜] Obs) : Prop :=
  ∀ ⦃f g : Test⦄, d f = d g → Φ f = Φ g

namespace DependsOnlyOnDifferential

/-- Any chosen differential-current representation implies intrinsic differential dependence. -/
theorem of_factors
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs} {J : OneForm →ₗ[𝕜] Obs}
    (h : FactorsThroughDifferential d Φ J) :
    DependsOnlyOnDifferential d Φ := by
  intro f g hfg
  rw [h f, h g, hfg]

/-- Intrinsic differential dependence is preserved by addition. -/
theorem add
    {d : Test →ₗ[𝕜] OneForm} {Φ Ψ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ)
    (hΨ : DependsOnlyOnDifferential d Ψ) :
    DependsOnlyOnDifferential d (Φ + Ψ) := by
  intro f g hfg
  simp only [LinearMap.add_apply]
  rw [hΦ hfg, hΨ hfg]

/-- Intrinsic differential dependence is preserved by scalar multiplication. -/
theorem smul
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ) (c : 𝕜) :
    DependsOnlyOnDifferential d (c • Φ) := by
  intro f g hfg
  simp only [LinearMap.smul_apply]
  rw [hΦ hfg]

/-- A transport functional depending only on `d f` vanishes whenever `d f = 0`. -/
theorem eq_zero_of_map_eq_zero
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs}
    (hΦ : DependsOnlyOnDifferential d Φ) {f : Test} (hf : d f = 0) :
    Φ f = 0 := by
  calc
    Φ f = Φ 0 := hΦ (by simpa using hf)
    _ = 0 := map_zero Φ

end DependsOnlyOnDifferential

/-- Representation-independent local balance data.

`transport` is defined on test objects themselves and is required only to depend on their
differentials.  A full `OneForm → Obs` current is deliberately not part of this structure. -/
structure IntrinsicBalanceLaw
    (δ : Obs →ₗ[𝕜] Obs)
    (Q : Test →ₗ[𝕜] Obs)
    (d : Test →ₗ[𝕜] OneForm) where
  /-- Intrinsic transport/flux on differential test data. -/
  transport : Test →ₗ[𝕜] Obs
  /-- Transport is insensitive to changes of a test object that leave its differential fixed. -/
  transport_depends : DependsOnlyOnDifferential d transport
  /-- Local source, sink, or torque functional. -/
  source : Test →ₗ[𝕜] Obs
  /-- The local balance identity. -/
  balance : ∀ f, δ (Q f) = transport f + source f

namespace IntrinsicBalanceLaw

/-- Evaluate an intrinsic balance law on one test object. -/
theorem apply
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d) (f : Test) :
    δ (Q f) = B.transport f + B.source f :=
  B.balance f

/-- Intrinsic transport vanishes on test objects annihilated by the differential. -/
theorem transport_eq_zero_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    B.transport f = 0 :=
  B.transport_depends.eq_zero_of_map_eq_zero hf

/-- If the differential test vanishes, only the source can change the localized quantity. -/
theorem evolution_eq_source_of_differential_eq_zero
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d) {f : Test} (hf : d f = 0) :
    δ (Q f) = B.source f := by
  rw [B.balance f, B.transport_eq_zero_of_differential_eq_zero hf, zero_add]

/-- In a source-free law, intrinsic flux is exactly the localized evolution. -/
theorem sourceFreeFlux_eq_evolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d) (hsource : B.source = 0) (f : Test) :
    B.transport f = δ (Q f) := by
  have h := B.balance f
  rw [hsource] at h
  simpa using h.symm

/-- Source-free intrinsic flux is unique for fixed evolution, localized quantity, and differential. -/
theorem sourceFreeFlux_unique
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B₁ B₂ : IntrinsicBalanceLaw δ Q d)
    (hsource₁ : B₁.source = 0) (hsource₂ : B₂.source = 0) (f : Test) :
    B₁.transport f = B₂.transport f := by
  calc
    B₁.transport f = δ (Q f) := B₁.sourceFreeFlux_eq_evolution hsource₁ f
    _ = B₂.transport f := (B₂.sourceFreeFlux_eq_evolution hsource₂ f).symm

/-- Scaling the evolution scales intrinsic transport and source. -/
noncomputable def scaleEvolution
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d) (c : 𝕜) :
    IntrinsicBalanceLaw (c • δ) Q d where
  transport := c • B.transport
  transport_depends := B.transport_depends.smul c
  source := c • B.source
  balance := by
    intro f
    simp only [LinearMap.smul_apply]
    rw [B.balance f]
    exact smul_add c (B.transport f) (B.source f)

/-- A represented balance law forgets its arbitrary extension away from exact differential data and
therefore determines an intrinsic balance law. -/
noncomputable def ofRepresented
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) :
    IntrinsicBalanceLaw δ Q d where
  transport := B.current.comp d
  transport_depends := by
    apply DependsOnlyOnDifferential.of_factors
    intro f
    rfl
  source := B.source
  balance := by
    intro f
    simpa using B.balance f

/-- Choosing an extension of intrinsic transport to all one-form-like tests recovers the represented
`BalanceLaw`.  This makes the full current functional explicitly downstream representation data. -/
noncomputable def toRepresented
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d)
    (J : OneForm →ₗ[𝕜] Obs)
    (hJ : FactorsThroughDifferential d B.transport J) :
    BalanceLaw δ Q d where
  current := J
  source := B.source
  balance := by
    intro f
    rw [B.balance f, hJ f]

/-- A chosen extension of intrinsic transport is precisely a differential current representation. -/
def toDifferentialCurrentRepresentation
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d)
    (J : OneForm →ₗ[𝕜] Obs)
    (hJ : FactorsThroughDifferential d B.transport J) :
    DifferentialCurrentRepresentation d B.transport where
  current := J
  factors := hJ

/-- If the source itself depends only on differential data, it may be absorbed into transport.
The resulting law is source-free without choosing any full current functional. -/
noncomputable def absorbSource
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : IntrinsicBalanceLaw δ Q d)
    (hsource : DependsOnlyOnDifferential d B.source) :
    IntrinsicBalanceLaw δ Q d where
  transport := B.transport + B.source
  transport_depends := B.transport_depends.add hsource
  source := 0
  balance := by
    intro f
    rw [B.balance f]
    simp

end IntrinsicBalanceLaw

end ConservationLaw
