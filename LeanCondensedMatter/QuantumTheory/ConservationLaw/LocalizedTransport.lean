import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution

set_option linter.style.header false

/-!
# Localized Heisenberg transport

Symmetric localization and differential current factorization are combined with the algebraic
Heisenberg generator on an arbitrary complex associative algebra. The same construction applies
to one-body, many-body, and bounded observable algebras without a choice of representation.

The transport and source functionals specialize the symmetric-localization construction to
the Heisenberg generator. Current representations and their extension ambiguity are supplied
by the representation-independent algebra in `Analysis.ConservationLaw.SymmetricLocalizationAlgebra`.
-/

namespace QuantumTheory
namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

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

end ConservationLaw
end QuantumTheory
