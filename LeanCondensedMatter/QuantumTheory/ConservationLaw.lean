import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra

set_option linter.style.header false

/-!
# Quantum conservation laws

The infinitesimal Heisenberg generator on a complex associative algebra is

```text
δₕ(A) = (i / ℏ) [h,A].
```

Its symmetric-product Leibniz rule gives localized transport and source functionals and
the intrinsic flux balance when transport factors through differential test data.
Linear realizations preserve the additive decomposition, while Lie homomorphisms
also intertwine the generator. Neither statement requires preservation of products.

Current representations and their extension ambiguity are supplied independently of
Heisenberg dynamics by `Analysis.ConservationLaw.SymmetricLocalizationAlgebra`.
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

/-- A linear observable realization preserves the additive decomposition of the
one-body symmetric-product derivative. No multiplication or Lie-bracket preservation is needed. -/
theorem map_heisenbergEvolution_symmetrizedProduct
    {B : Type*} [AddCommGroup B] [Module ℂ B]
    (L : 𝒜 →ₗ[ℂ] B) (ℏ : ℝ) (h A C : 𝒜) :
    L (heisenbergEvolution ℏ h (LinearMap.symmetrizedProduct (K := ℂ) A C)) =
      L (LinearMap.symmetrizedProduct (K := ℂ) (heisenbergEvolution ℏ h A) C) +
        L (LinearMap.symmetrizedProduct (K := ℂ) A (heisenbergEvolution ℏ h C)) := by
  rw [heisenbergEvolution_symmetrizedProduct, map_add]

/-- A complex Lie algebra homomorphism intertwines the infinitesimal Heisenberg generators.
Unlike the linear realization of a decomposition, this uses preservation of the Lie bracket. -/
theorem map_heisenbergEvolution
    {B : Type*} [Ring B] [Algebra ℂ B]
    (L : 𝒜 →ₗ⁅ℂ⁆ B) (ℏ : ℝ) (h A : 𝒜) :
    L (heisenbergEvolution ℏ h A) = heisenbergEvolution ℏ (L h) (L A) := by
  simp only [heisenbergEvolution_apply, map_smul, LieHom.map_lie]

section LocalizedTransport

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- The symmetrically localized transport functional in Heisenberg normalization. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) :
    Test →ₗ[ℂ] 𝒜 :=
  _root_.ConservationLaw.localizedQuantityFunctional ((heisenbergEvolution ℏ h).comp M) m

/-- The symmetrically localized source/torque functional in Heisenberg normalization. -/
noncomputable def heisenbergSourceFunctional
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) :
    Test →ₗ[ℂ] 𝒜 :=
  _root_.ConservationLaw.localizedQuantityFunctional M (heisenbergEvolution ℏ h m)

@[simp]
theorem heisenbergTransportFunctional_apply
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) (f : Test) :
    heisenbergTransportFunctional ℏ h M m f =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (heisenbergEvolution ℏ h (M f)) m :=
  rfl

@[simp]
theorem heisenbergSourceFunctional_apply
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) (f : Test) :
    heisenbergSourceFunctional ℏ h M m f =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (M f) (heisenbergEvolution ℏ h m) :=
  rfl

/-- Heisenberg evolution of a symmetrically localized quantity gives the intrinsic balance
law as soon as its transport functional depends only on differential test data.  No extension of
that transport to arbitrary one-form-like data is chosen here. -/
noncomputable def heisenbergIntrinsicSymmetricLocalizationBalanceLaw
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (htransport : Function.FactorsThrough
      (heisenbergTransportFunctional ℏ h M m) d) :
    _root_.ConservationLaw.FluxBalanceLaw
      (heisenbergEvolution ℏ h)
      (_root_.ConservationLaw.localizedQuantityFunctional M m)
      d where
  transport := heisenbergTransportFunctional ℏ h M m
  transport_depends := htransport
  source := heisenbergSourceFunctional ℏ h M m
  balance := by
    apply LinearMap.ext
    intro f
    exact heisenbergEvolution_symmetrizedProduct ℏ h (M f) m

end LocalizedTransport

end ConservationLaw
end QuantumTheory
