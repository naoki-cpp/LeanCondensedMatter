import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation

set_option linter.style.header false

/-!
# Equivalence of differential current representations

A differential current functional is physically observed by a transport law only on exact test
one-forms `d f`.  This module records that representation ambiguity explicitly: two full current
functionals are equivalent when they agree on every exact differential.

This is distinct from current/source ambiguity in `BalanceLaw`.  Here the represented transport
functional is fixed; only the extension away from `range d` is allowed to vary.  The same module
also owns weak equivalence and uniqueness criteria for concrete current-density representations.
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

/-- A current functional is invisible to the transport law when it vanishes on every exact
differential.  Such a functional is pure extension ambiguity away from `range d`. -/
def DifferentialCurrentInvisible
    (d : Test →ₗ[𝕜] OneForm)
    (K : OneForm →ₗ[𝕜] Obs) : Prop :=
  ∀ f, K (d f) = 0

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
    exact LinearMap.ext h
  · intro h f
    simpa using congrArg (fun L : Test →ₗ[𝕜] Obs => L f) h

end DifferentialCurrentEquivalent

namespace DifferentialCurrentRepresentation

section Ring

variable {R Test' OneForm' Obs' : Type*}
variable [CommRing R]
variable [AddCommMonoid Test'] [Module R Test']
variable [AddCommMonoid OneForm'] [Module R OneForm']
variable [AddCommGroup Obs'] [Module R Obs']

/-- Any two representations of the same intrinsic transport differ by a current functional that is
invisible on exact differentials.  Equivalently, one representative is the other plus arbitrary
extension data away from `range d`. -/
theorem exists_current_eq_add_invisible
    {d : Test' →ₗ[R] OneForm'} {Φ : Test' →ₗ[R] Obs'}
    (R₁ R₂ : DifferentialCurrentRepresentation d Φ) :
    ∃ K : OneForm' →ₗ[R] Obs',
      DifferentialCurrentInvisible d K ∧ R₁.current = R₂.current + K := by
  refine ⟨R₁.current - R₂.current, ?_, ?_⟩
  · intro f
    change R₁.current (d f) - R₂.current (d f) = 0
    have h : R₁.current.comp d = R₂.current.comp d :=
      R₁.isCurrent.symm.trans R₂.isCurrent
    have hf := congrArg (fun L : Test' →ₗ[R] Obs' => L f) h
    simp only [LinearMap.comp_apply] at hf
    rw [hf]
    simp
  · ext α
    change R₁.current α = R₂.current α + (R₁.current α - R₂.current α)
    module

end Ring

end DifferentialCurrentRepresentation


section CurrentDensity

variable {CurrentDensity : Type*}
variable [AddCommMonoid CurrentDensity] [Module 𝕜 CurrentDensity]

/-- Two current densities are weakly equivalent when their paired current functionals
agree on every exact test 1-form `d f`. -/
def CurrentDensityEquivalent
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j₁ j₂ : CurrentDensity) : Prop :=
  DifferentialCurrentEquivalent d (pairing j₁) (pairing j₂)

namespace CurrentDensityEquivalent

/-- Weak current-density equivalence is reflexive. -/
theorem refl
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity))
    (j : CurrentDensity) :
    CurrentDensityEquivalent d pairing j j :=
  DifferentialCurrentEquivalent.refl d (pairing j)

/-- Weak current-density equivalence is symmetric. -/
theorem symm
    {d : Test →ₗ[𝕜] OneForm}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ : CurrentDensity}
    (h : CurrentDensityEquivalent d pairing j₁ j₂) :
    CurrentDensityEquivalent d pairing j₂ j₁ :=
  DifferentialCurrentEquivalent.symm h

/-- Weak current-density equivalence is transitive. -/
theorem trans
    {d : Test →ₗ[𝕜] OneForm}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    {j₁ j₂ j₃ : CurrentDensity}
    (h₁₂ : CurrentDensityEquivalent d pairing j₁ j₂)
    (h₂₃ : CurrentDensityEquivalent d pairing j₂ j₃) :
    CurrentDensityEquivalent d pairing j₁ j₃ :=
  DifferentialCurrentEquivalent.trans h₁₂ h₂₃

end CurrentDensityEquivalent

namespace LocalCurrentDensityRepresentation

/-- Any two densities representing the same transport functional are weakly equivalent on exact
test 1-forms. -/
theorem currentDensityEquivalent
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    CurrentDensityEquivalent d pairing R₁.currentDensity R₂.currentDensity :=
  DifferentialCurrentEquivalent.iff_comp_eq.mpr
    (R₁.isCurrentDensity.symm.trans R₂.isCurrentDensity)

end LocalCurrentDensityRepresentation

/-- Exact differential tests and the chosen pairing separate current densities when weak
equivalence implies equality. -/
def SeparatesCurrentDensities
    (d : Test →ₗ[𝕜] OneForm)
    (pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)) : Prop :=
  ∀ ⦃j₁ j₂ : CurrentDensity⦄, CurrentDensityEquivalent d pairing j₁ j₂ → j₁ = j₂

/-- A local current density is unique when the concrete differential tests and pairing separate
current densities. -/
theorem localCurrentDensity_unique_of_separates
    {d : Test →ₗ[𝕜] OneForm}
    {Φ : Test →ₗ[𝕜] Obs}
    {pairing : LocalCurrentPairing (𝕜 := 𝕜) (OneForm := OneForm) (Obs := Obs)
      (CurrentDensity := CurrentDensity)}
    (hsep : SeparatesCurrentDensities d pairing)
    (R₁ R₂ : LocalCurrentDensityRepresentation d Φ pairing) :
    R₁.currentDensity = R₂.currentDensity :=
  hsep (R₁.currentDensityEquivalent R₂)

end CurrentDensity

end ConservationLaw
