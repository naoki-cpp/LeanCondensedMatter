import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw

set_option linter.style.header false

/-!
# Flux/represented balance-law adapters

This module owns conversions between the representation-independent `FluxBalanceLaw` and the
represented `BalanceLaw`, together with the operation that chooses a full differential-current
representation for representation-independent transport.  The flux-balance semantic owner does not import this module.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

namespace FluxBalanceLaw

/-- A represented balance law forgets its arbitrary extension away from exact differential data and
therefore determines an representation-independent balance law. -/
noncomputable def ofRepresented
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) :
    FluxBalanceLaw δ Q d where
  transport := B.current.comp d
  transport_depends := by
    intro f g hfg
    exact congrArg B.current hfg
  source := B.source
  balance := by
    intro f
    simpa using B.balance f

/-- Choosing an extension of representation-independent transport to all one-form-like tests recovers the represented
`BalanceLaw`.  This makes the full current functional explicitly downstream representation data. -/
noncomputable def toRepresented
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d)
    (J : OneForm →ₗ[𝕜] Obs)
    (hJ : B.transport = J.comp d) :
    BalanceLaw δ Q d where
  current := J
  source := B.source
  balance := by
    intro f
    rw [B.balance f]
    have hf := congrArg (fun L : Test →ₗ[𝕜] Obs => L f) hJ
    simp only [LinearMap.comp_apply] at hf
    rw [hf]

/-- A chosen extension of representation-independent transport is precisely a differential current representation. -/
def toDifferentialCurrentRepresentation
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : FluxBalanceLaw δ Q d)
    (J : OneForm →ₗ[𝕜] Obs)
    (hJ : B.transport = J.comp d) :
    DifferentialCurrentRepresentation d B.transport where
  current := J
  isCurrent := hJ

end FluxBalanceLaw

end ConservationLaw
