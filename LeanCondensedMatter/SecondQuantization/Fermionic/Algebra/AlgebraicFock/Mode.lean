import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Annihilation
import Mathlib.Analysis.InnerProductSpace.Orthonormal

set_option linter.style.header false

/-!
# Mode fields from an orthonormal one-particle family

An orthonormal family `e : Mode → 𝓗₁` defines mode creation and annihilation operators by smearing
the basis-independent fields with `e i`:

```text
cᵢ† = a†(eᵢ),
cᵢ  = a(eᵢ).
```

The smeared canonical anticommutation relations then specialize to the usual Kronecker-delta mode
relations.
-/

namespace SecondQuantization
namespace Fermionic
namespace AlgebraicFock

variable {Mode 𝓗₁ : Type*}
variable [NormedAddCommGroup 𝓗₁] [InnerProductSpace ℂ 𝓗₁]

/-- Creation in mode `i`, obtained by smearing with the corresponding one-particle vector. -/
noncomputable def modeCreate (e : Mode → 𝓗₁) (i : Mode) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  create 𝓗₁ (e i)

/-- Annihilation in mode `i`, obtained by smearing with the corresponding one-particle vector. -/
noncomputable def modeAnnihilate (e : Mode → 𝓗₁) (i : Mode) :
    AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁ :=
  annihilate 𝓗₁ (e i)

@[simp]
theorem modeCreate_apply (e : Mode → 𝓗₁) (i : Mode) (Ψ : AlgebraicFock 𝓗₁) :
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
          (LinearMap.id : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) := by
  classical
  rw [modeAnnihilate, modeCreate, annihilate_comp_create_add_swap]
  rw [(orthonormal_iff_ite.mp he) i j]

/-- The same-mode mixed anticommutator is the identity. -/
@[simp]
theorem modeAnnihilate_comp_modeCreate_add_self
    {e : Mode → 𝓗₁} (he : Orthonormal ℂ e) (i : Mode) :
    (modeAnnihilate e i).comp (modeCreate e i) +
      (modeCreate e i).comp (modeAnnihilate e i) =
        (LinearMap.id : AlgebraicFock 𝓗₁ →ₗ[ℂ] AlgebraicFock 𝓗₁) := by
  classical
  simpa using modeAnnihilate_comp_modeCreate_add_swap he i i

/-- Distinct modes have zero mixed anticommutator. -/
theorem modeAnnihilate_comp_modeCreate_add_of_ne
    {e : Mode → 𝓗₁} (he : Orthonormal ℂ e) {i j : Mode} (hij : i ≠ j) :
    (modeAnnihilate e i).comp (modeCreate e j) +
      (modeCreate e j).comp (modeAnnihilate e i) = 0 := by
  classical
  simpa [hij] using modeAnnihilate_comp_modeCreate_add_swap he i j

end AlgebraicFock
end Fermionic
end SecondQuantization
