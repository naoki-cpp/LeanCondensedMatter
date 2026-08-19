import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation

set_option linter.style.header false

/-!
# Equivalence of differential current representations

A differential current functional is physically observed by a transport law only on exact test
one-forms `d f`.  This module records that representation ambiguity explicitly: two full current
functionals are equivalent when they agree on every exact differential.

This is distinct from current/source ambiguity in `BalanceLaw`.  Here the represented transport
functional is fixed; only the extension away from `range d` is allowed to vary.
-/

namespace ConservationLaw

variable {𝕜 Test OneForm Obs : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid Test] [Module 𝕜 Test]
variable [AddCommMonoid OneForm] [Module 𝕜 OneForm]
variable [AddCommMonoid Obs] [Module 𝕜 Obs]

/-- Two full current functionals are equivalent when they agree on every exact differential
`d f`.  They may differ away from `range d`. -/
def DifferentialCurrentEquivalent
    (d : Test →ₗ[𝕜] OneForm)
    (J₁ J₂ : OneForm →ₗ[𝕜] Obs) : Prop :=
  ∀ f, J₁ (d f) = J₂ (d f)

namespace DifferentialCurrentEquivalent

/-- Differential-current equivalence is reflexive. -/
theorem refl
    (d : Test →ₗ[𝕜] OneForm) (J : OneForm →ₗ[𝕜] Obs) :
    DifferentialCurrentEquivalent d J J := by
  intro f
  rfl

/-- Differential-current equivalence is symmetric. -/
theorem symm
    {d : Test →ₗ[𝕜] OneForm} {J₁ J₂ : OneForm →ₗ[𝕜] Obs}
    (h : DifferentialCurrentEquivalent d J₁ J₂) :
    DifferentialCurrentEquivalent d J₂ J₁ := by
  intro f
  exact (h f).symm

/-- Differential-current equivalence is transitive. -/
theorem trans
    {d : Test →ₗ[𝕜] OneForm} {J₁ J₂ J₃ : OneForm →ₗ[𝕜] Obs}
    (h₁₂ : DifferentialCurrentEquivalent d J₁ J₂)
    (h₂₃ : DifferentialCurrentEquivalent d J₂ J₃) :
    DifferentialCurrentEquivalent d J₁ J₃ := by
  intro f
  exact (h₁₂ f).trans (h₂₃ f)

/-- Agreement on exact differentials is exactly equality after precomposition with `d`. -/
theorem iff_comp_eq
    {d : Test →ₗ[𝕜] OneForm} {J₁ J₂ : OneForm →ₗ[𝕜] Obs} :
    DifferentialCurrentEquivalent d J₁ J₂ ↔ J₁.comp d = J₂.comp d := by
  constructor
  · intro h
    apply LinearMap.ext
    intro f
    exact h f
  · intro h f
    simpa using congrArg (fun L : Test →ₗ[𝕜] Obs => L f) h

end DifferentialCurrentEquivalent

namespace DifferentialCurrentRepresentation

/-- Any two current functionals representing the same intrinsic transport are equivalent on exact
differentials. -/
theorem currentEquivalent
    {d : Test →ₗ[𝕜] OneForm} {Φ : Test →ₗ[𝕜] Obs}
    (R₁ R₂ : DifferentialCurrentRepresentation d Φ) :
    DifferentialCurrentEquivalent d R₁.current R₂.current := by
  intro f
  calc
    R₁.current (d f) = Φ f := (R₁.factors f).symm
    _ = R₂.current (d f) := R₂.factors f

end DifferentialCurrentRepresentation

end ConservationLaw
