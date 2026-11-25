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
current representation or balance law. The generator acts on any unital associative complex
algebra; an endomorphism algebra is only one realization.
-/

namespace QuantumTheory
namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

/-- Scalar converting a commutator with the Hamiltonian into the Heisenberg derivative. -/
noncomputable def heisenbergScale (ℏ : ℝ) : ℂ :=
  Complex.I / (ℏ : ℂ)

/-- The infinitesimal Heisenberg evolution as a linear endomorphism of a complex associative algebra. -/
noncomputable def heisenbergEvolution
    (ℏ : ℝ) (h : 𝒜) :
    𝒜 →ₗ[ℂ] 𝒜 :=
  heisenbergScale ℏ • LieAlgebra.ad ℂ 𝒜 h

@[simp]
theorem heisenbergEvolution_apply
    (ℏ : ℝ) (h A : 𝒜) :
    heisenbergEvolution ℏ h A =
      heisenbergScale ℏ • ⁅h, A⁆ :=
  rfl

/-- Heisenberg evolution satisfies the symmetric-product Leibniz rule.
This is the scaled form of the existing associative-algebra commutator identity. -/
theorem heisenbergEvolution_symmetrizedProduct
    (ℏ : ℝ) (h A B : 𝒜) :
    heisenbergEvolution ℏ h (LinearMap.symmetrizedProduct (K := ℂ) A B) =
      LinearMap.symmetrizedProduct (K := ℂ) (heisenbergEvolution ℏ h A) B +
        LinearMap.symmetrizedProduct (K := ℂ) A (heisenbergEvolution ℏ h B) := by
  simp only [heisenbergEvolution_apply, LinearMap.lie_symmetrizedProduct, smul_add]
  have hleft :=
    (((LinearMap.symmetrizedProductBilinear (K := ℂ) 𝒜).flip B).map_smul
      (heisenbergScale ℏ) ⁅h, A⁆).symm
  have hright :=
    ((LinearMap.symmetrizedProductBilinear (K := ℂ) 𝒜 A).map_smul
      (heisenbergScale ℏ) ⁅h, B⁆).symm
  exact congrArg₂ (· + ·) hleft hright

end ConservationLaw
end QuantumTheory
