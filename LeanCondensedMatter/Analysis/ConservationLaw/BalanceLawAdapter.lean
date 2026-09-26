import LeanCondensedMatter.Analysis.ConservationLaw.BalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.IntrinsicBalanceLaw

set_option linter.style.header false

/-!
# Represented/intrinsic balance-law adapters

This module owns conversions between the representation-independent `IntrinsicBalanceLaw` and the
represented `BalanceLaw`, together with the operation that chooses a full differential-current
representation for intrinsic transport.  The intrinsic semantic owner does not import this module.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

namespace IntrinsicBalanceLaw

/-- A represented balance law forgets its arbitrary extension away from exact differential data and
therefore determines an intrinsic balance law. -/
noncomputable def ofRepresented
    {δ : Obs →ₗ[𝕜] Obs}
    {Q : Test →ₗ[𝕜] Obs}
    {d : Test →ₗ[𝕜] OneForm}
    (B : BalanceLaw δ Q d) :
    IntrinsicBalanceLaw δ Q d where
  transport := B.current.comp d
  transport_depends := DependsOnlyOnDifferential.of_isDifferentialCurrent (fun _ => rfl)
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
    (hJ : IsDifferentialCurrent d B.transport J) :
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
    (hJ : IsDifferentialCurrent d B.transport J) :
    DifferentialCurrentRepresentation d B.transport where
  current := J
  factors := hJ

end IntrinsicBalanceLaw

end ConservationLaw
