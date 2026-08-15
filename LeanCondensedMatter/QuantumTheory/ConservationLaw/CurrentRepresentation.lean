import LeanCondensedMatter.Analysis.Calculus.CurrentRepresentation
import LeanCondensedMatter.Analysis.Calculus.OneBodyBalance

set_option linter.style.header false

/-!
# Generalized one-body transport functionals

The representation-independent weak-current abstractions live in
`Analysis.Calculus.CurrentRepresentation` under the root `ConservationLaw` namespace. This module
packages the canonical one-body transport commutator as a complex-linear functional of localization
tests and proves how differential factorizations lift to generalized quantities.

No second-quantization or particle-statistics input is used here.
-/

namespace QuantumTheory
namespace ConservationLaw

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The canonical transport term packaged as a linear functional of the localization test object. -/
noncomputable def transportFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := _root_.ConservationLaw.transportCommutator V h M m
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.transportCommutator,
      _root_.ConservationLaw.symmetrizedProduct,
      _root_.ConservationLaw.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.transportCommutator,
      _root_.ConservationLaw.symmetrizedProduct,
      _root_.ConservationLaw.linearCommutator]
    module

@[simp]
theorem transportFunctional_apply
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) (f : Test) :
    transportFunctional V h M m f =
      _root_.ConservationLaw.transportCommutator V h M m f :=
  rfl

/-- Symmetrization with a fixed one-body quantity is linear in the transport operator. -/
noncomputable def symmetrizedProductRightLinear
    (m : V →ₗ[ℂ] V) :
    (V →ₗ[ℂ] V) →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := fun A => _root_.ConservationLaw.symmetrizedProduct A m
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.symmetrizedProduct]
    module
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.symmetrizedProduct]
    module

@[simp]
theorem symmetrizedProductRightLinear_apply
    (m A : V →ₗ[ℂ] V) :
    symmetrizedProductRightLinear V m A = _root_.ConservationLaw.symmetrizedProduct A m :=
  rfl

/-- The bare localization commutator `f ↦ [h, M(f)]`, packaged linearly. -/
noncomputable def localizationCommutatorFunctional
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    Test →ₗ[ℂ] (V →ₗ[ℂ] V) where
  toFun := fun f => _root_.ConservationLaw.linearCommutator h (M f)
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.linearCommutator]
    module
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro v
    simp [_root_.ConservationLaw.linearCommutator]
    module

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (f : Test) :
    localizationCommutatorFunctional V h M f =
      _root_.ConservationLaw.linearCommutator h (M f) :=
  rfl

/-- The generalized transport functional is obtained by postcomposing the bare localization
commutator with symmetrization by `m`. -/
theorem transportFunctional_eq_symmetrizedProductRight_comp
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V) :
    transportFunctional V h M m =
      (symmetrizedProductRightLinear V m).comp
        (localizationCommutatorFunctional V h M) := by
  apply LinearMap.ext
  intro f
  rfl

/-- Any differential factorization of the bare localization commutator induces one for the canonical
transport functional of an arbitrary one-body quantity `m`. -/
theorem factorsThroughDifferential_transport
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hJ : _root_.ConservationLaw.FactorsThroughDifferential d
      (localizationCommutatorFunctional V h M) J) :
    _root_.ConservationLaw.FactorsThroughDifferential d
      (transportFunctional V h M m)
      ((symmetrizedProductRightLinear V m).comp J) := by
  rw [transportFunctional_eq_symmetrizedProductRight_comp]
  exact _root_.ConservationLaw.FactorsThroughDifferential.postcomp hJ
    (symmetrizedProductRightLinear V m)

/-- For `m = q I`, the generalized transport functional is exactly `q` times the bare localization
commutator functional. -/
theorem transportFunctional_smul_id
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) :
    transportFunctional V h M (q • LinearMap.id) =
      q • localizationCommutatorFunctional V h M := by
  apply LinearMap.ext
  intro f
  simp [transportFunctional, localizationCommutatorFunctional,
    _root_.ConservationLaw.transportCommutator]

/-- Any differential factorization of the bare localization commutator induces the corresponding
charge-current factorization for `m = q I`. -/
theorem factorsThroughDifferential_transport_smul_id
    (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (d : Test →ₗ[ℂ] OneForm)
    (J : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (q : ℂ)
    (hJ : _root_.ConservationLaw.FactorsThroughDifferential d
      (localizationCommutatorFunctional V h M) J) :
    _root_.ConservationLaw.FactorsThroughDifferential d
      (transportFunctional V h M (q • LinearMap.id)) (q • J) := by
  rw [transportFunctional_smul_id]
  exact _root_.ConservationLaw.FactorsThroughDifferential.smul hJ q

end ConservationLaw
end QuantumTheory
