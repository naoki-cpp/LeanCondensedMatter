import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation
import LeanCondensedMatter.Analysis.ConservationLaw.FluxBalanceLaw
import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra
import LeanCondensedMatter.QuantumTheory.ConservationLaw.HeisenbergEvolution

set_option linter.style.header false

/-!
# Localized Heisenberg transport

Symmetric localization and differential current factorization are combined with the algebraic
Heisenberg generator on an arbitrary complex associative algebra. The same construction applies
to one-body, many-body, and bounded observable algebras without a choice of representation.

No particular current-density formula is selected here. The fundamental transport object is the
functional on differential test data. A formula such as `1/2 {v,m}` is a downstream representation
of that functional under additional assumptions.
-/

namespace QuantumTheory
namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

/-- The localization commutator scaled to the physical Heisenberg derivative. -/
noncomputable def heisenbergLocalizationFunctional
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜) :
    Test →ₗ[ℂ] 𝒜 :=
  (heisenbergEvolution ℏ h).comp M

/-- The symmetrically localized transport functional in Heisenberg normalization. -/
noncomputable def heisenbergTransportFunctional
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) :
    Test →ₗ[ℂ] 𝒜 :=
  _root_.ConservationLaw.localizedQuantityFunctional (heisenbergLocalizationFunctional ℏ h M) m

/-- The symmetrically localized source/torque functional in Heisenberg normalization. -/
noncomputable def heisenbergSourceFunctional
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m : 𝒜) :
    Test →ₗ[ℂ] 𝒜 :=
  _root_.ConservationLaw.localizedQuantityFunctional M (heisenbergEvolution ℏ h m)

@[simp]
theorem heisenbergLocalizationFunctional_apply
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜) (f : Test) :
    heisenbergLocalizationFunctional ℏ h M f =
      heisenbergScale ℏ • ⁅h, M f⁆ :=
  rfl

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

/-- A one-form-like test is paired with an algebra-valued current density by symmetric
localization. This pairing does not choose which current density represents a given transport
functional. -/
noncomputable def operatorLocalCurrentPairing
    (N : OneForm →ₗ[ℂ] 𝒜) :
    _root_.ConservationLaw.LocalCurrentPairing
      (𝕜 := ℂ)
      (OneForm := OneForm)
      (Obs := 𝒜)
      (CurrentDensity := 𝒜) :=
  ((LinearMap.llcomp ℂ OneForm 𝒜 𝒜).flip N).comp
    (LinearMap.flip (_root_.LinearMap.symmetrizedProductBilinear (K := ℂ) 𝒜))

@[simp]
theorem operatorLocalCurrentPairing_apply
    (N : OneForm →ₗ[ℂ] 𝒜)
    (current : 𝒜) (α : OneForm) :
    operatorLocalCurrentPairing N current α =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) (N α) current :=
  rfl

end ConservationLaw
end QuantumTheory
