import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option linter.style.header false

/-!
# Mode fields from an orthonormal one-particle family

This module completes the mode-recovery part of F2 in issue #524. Given an orthonormal family
`e : Mode → 𝓗₁` in the one-particle Hilbert space, its vectors smear the basis-independent fields:

```text
cᵢ† = a†(eᵢ),
cᵢ  = a(eᵢ).
```

The smeared CAR then specialize to the usual Kronecker-delta mode relations. This does not yet
identify the exterior-algebra Fock representation with the existing occupation-subset
representation; that comparison requires a basis-induced algebra equivalence and remains a
separate slice.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

variable {Mode 𝓗₁ : Type*}
variable [DecidableEq Mode]
variable [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- Creation in mode `i`, obtained by smearing with the corresponding one-particle vector. -/
noncomputable def modeCreate (e : Mode → 𝓗₁) (i : Mode) :
    FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
  create 𝓗₁ (e i)

/-- Annihilation in mode `i`, obtained by smearing with the corresponding one-particle vector. -/
noncomputable def modeAnnihilate (e : Mode → 𝓗₁) (i : Mode) :
    FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁ :=
  annihilate 𝓗₁ (e i)

@[simp]
theorem modeCreate_apply (e : Mode → 𝓗₁) (i : Mode) (Ψ : FiniteParticleFock 𝓗₁) :
    modeCreate e i Ψ = oneParticle 𝓗₁ (e i) * Ψ :=
  rfl

@[simp]
theorem modeAnnihilate_vacuum (e : Mode → 𝓗₁) (i : Mode) :
    modeAnnihilate e i (vacuum 𝓗₁) = 0 := by
  simpa [modeAnnihilate] using annihilate_vacuum 𝓗₁ (e i)

/-- Creation operators attached to any one-particle family anticommute. -/
theorem modeCreate_comp_add_swap (e : Mode → 𝓗₁) (i j : Mode) :
    (modeCreate e i).comp (modeCreate e j) +
      (modeCreate e j).comp (modeCreate e i) = 0 := by
  simpa [modeCreate] using create_comp_add_swap 𝓗₁ (e i) (e j)

/-- Annihilation operators attached to any one-particle family anticommute. -/
theorem modeAnnihilate_comp_add_swap (e : Mode → 𝓗₁) (i j : Mode) :
    (modeAnnihilate e i).comp (modeAnnihilate e j) +
      (modeAnnihilate e j).comp (modeAnnihilate e i) = 0 := by
  simpa [modeAnnihilate] using annihilate_comp_add_swap 𝓗₁ (e i) (e j)

/-- For an orthonormal family, the mixed smeared CAR becomes the Kronecker-delta mode CAR. -/
theorem modeAnnihilate_comp_modeCreate_add_swap
    {e : Mode → 𝓗₁} (he : Orthonormal ℂ e) (i j : Mode) :
    (modeAnnihilate e i).comp (modeCreate e j) +
      (modeCreate e j).comp (modeAnnihilate e i) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁) := by
  rw [modeAnnihilate, modeCreate, annihilate_comp_create_add_swap]
  rw [(orthonormal_iff_ite.mp he) i j]

/-- The same-mode mixed anticommutator is the identity. -/
@[simp]
theorem modeAnnihilate_comp_modeCreate_add_self
    {e : Mode → 𝓗₁} (he : Orthonormal ℂ e) (i : Mode) :
    (modeAnnihilate e i).comp (modeCreate e i) +
      (modeCreate e i).comp (modeAnnihilate e i) =
        (LinearMap.id : FiniteParticleFock 𝓗₁ →ₗ[ℂ] FiniteParticleFock 𝓗₁) := by
  simpa using modeAnnihilate_comp_modeCreate_add_swap he i i

/-- Distinct modes have zero mixed anticommutator. -/
theorem modeAnnihilate_comp_modeCreate_add_of_ne
    {e : Mode → 𝓗₁} (he : Orthonormal ℂ e) {i j : Mode} (hij : i ≠ j) :
    (modeAnnihilate e i).comp (modeCreate e j) +
      (modeCreate e j).comp (modeAnnihilate e i) = 0 := by
  simpa [hij] using modeAnnihilate_comp_modeCreate_add_swap he i j

end Field
end Fermionic
end SecondQuantization
