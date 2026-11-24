import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import Mathlib.Basic.Complex.Basic

set_option linter.style.header false

/-!
# Algebraic Heisenberg evolution

This module supplies only the quantum-mechanical normalization of algebraic commutator evolution:

```text
δₕ(A) = (i / ℏ) [h,A].
```

It does not choose a localization map, transported quantity, position observable, velocity, or
current representation or balance law.
-/

namespace QuantumTheory
namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- Heisenberg evolution as a linear endomorphism of the one-body operator space. -/
noncomputable def heisenbergEvolution
    (ℏ : ℝ) (h : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  heisenbergScale ℏ • LieAlgebra.ad ℂ (Module.End ℂ V) h

@[simp]
theorem heisenbergEvolution_apply
    (ℏ : ℝ) (h A : V →ₗ[ℂ] V) :
    heisenbergEvolution V ℏ h A =
      heisenbergScale ℏ • ⁅h, A⁆ :=
  rfl

/-- Heisenberg evolution satisfies the symmetric-product Leibniz rule.
This is the scaled form of the existing associative-algebra commutator identity. -/
theorem heisenbergEvolution_symmetrizedProduct
    (ℏ : ℝ) (h A B : V →ₗ[ℂ] V) :
    heisenbergEvolution V ℏ h (LinearMap.symmetrizedProduct (K := ℂ) A B) =
      LinearMap.symmetrizedProduct (K := ℂ) (heisenbergEvolution V ℏ h A) B +
        LinearMap.symmetrizedProduct (K := ℂ) A (heisenbergEvolution V ℏ h B) := by
  simp only [heisenbergEvolution_apply, LinearMap.lie_symmetrizedProduct, smul_add]
  have hleft :=
    (((LinearMap.symmetrizedProductBilinear (K := ℂ) (V →ₗ[ℂ] V)).flip B).map_smul
      (heisenbergScale ℏ) ⁅h, A⁆).symm
  have hright :=
    ((LinearMap.symmetrizedProductBilinear (K := ℂ) (V →ₗ[ℂ] V) A).map_smul
      (heisenbergScale ℏ) ⁅h, B⁆).symm
  exact congrArg₂ (· + ·) hleft hright

end ConservationLaw
end QuantumTheory
