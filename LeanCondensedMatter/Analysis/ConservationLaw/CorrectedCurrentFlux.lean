import LeanCondensedMatter.Analysis.ConservationLaw.SymmetricLocalizationAlgebra

set_option linter.style.header false

/-!
# Corrected symmetrized-current flux algebra

This module packages the pure operator algebra behind the decomposition of a nested localized
transport into a symmetrized-current contribution and a localization correction.
No Heisenberg dynamics, first-quantized velocity semantics, second quantization, or response theory
is assumed here.

For an operator-valued one-form localizer `N`, a distinguished operator `v`, and transported
quantity `m`, define

```text
J_nested(α) = 1/2 { 1/2 {N α, v}, m }
J_sym(α)   = 1/2 { N α, 1/2 {v,m} }
J_corr      = J_nested - J_sym.
```

Then

```text
J_corr(α) = 1/4 [v,[N α,m]].
```

These are current-functionals on supplied one-form-like data.  Whether they represent an intrinsic
transport through a differential is a separate downstream statement.
-/

namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K OneForm : Type*} [Field K]
variable [AddCommGroup OneForm] [Module K OneForm]
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- Full nested symmetrized flux on one-form-like localization data. -/
noncomputable def nestedSymmetrizedCurrentFlux
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) :
    OneForm →ₗ[K] (V →ₗ[K] V) :=
  localizedQuantityFunctional V (localizedQuantityFunctional V N velocity) m

@[simp]
theorem nestedSymmetrizedCurrentFlux_apply
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) (α : OneForm) :
    nestedSymmetrizedCurrentFlux V velocity m N α =
      LinearMap.symmetrizedProduct (K := K) (LinearMap.symmetrizedProduct (K := K) (N α) velocity) m :=
  rfl

/-- Flux obtained from the symmetrized current `1/2 {v,m}`. -/
noncomputable def symmetrizedCurrentFlux
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) :
    OneForm →ₗ[K] (V →ₗ[K] V) :=
  localizedQuantityFunctional V N (LinearMap.symmetrizedProduct (K := K) velocity m)

@[simp]
theorem symmetrizedCurrentFlux_apply
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) (α : OneForm) :
    symmetrizedCurrentFlux V velocity m N α =
      LinearMap.symmetrizedProduct (K := K) (N α) (LinearMap.symmetrizedProduct (K := K) velocity m) :=
  rfl

/-- Canonical localization correction, defined as the exact difference between the nested and
symmetrized fluxes. -/
noncomputable def localizationCorrectionCurrentFlux
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) :
    OneForm →ₗ[K] (V →ₗ[K] V) :=
  nestedSymmetrizedCurrentFlux V velocity m N -
    symmetrizedCurrentFlux V velocity m N

@[simp]
theorem localizationCorrectionCurrentFlux_apply
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) (α : OneForm) :
    localizationCorrectionCurrentFlux V velocity m N α =
      (1 / 4 : K) • ⁅velocity, ⁅N α, m⁆⁆ := by
  change
    LinearMap.symmetrizedProduct (K := K) (LinearMap.symmetrizedProduct (K := K) (N α) velocity) m -
      LinearMap.symmetrizedProduct (K := K) (N α) (LinearMap.symmetrizedProduct (K := K) velocity m) = _
  rw [LinearMap.symmetrizedProduct_nested, add_comm, add_sub_cancel_right]

/-- The nested flux is exactly the symmetrized flux plus localization correction. -/
theorem nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) :
    nestedSymmetrizedCurrentFlux V velocity m N =
      symmetrizedCurrentFlux V velocity m N +
        localizationCorrectionCurrentFlux V velocity m N := by
  unfold localizationCorrectionCurrentFlux
  rw [add_comm, sub_add_cancel]

/-- If every supplied localizer commutes with `m`, the localization correction vanishes. -/
theorem localizationCorrectionCurrentFlux_eq_zero_of_commutes
    (velocity m : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V))
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    localizationCorrectionCurrentFlux V velocity m N = 0 := by
  apply LinearMap.ext
  intro α
  rw [localizationCorrectionCurrentFlux_apply V velocity m N α, hcomm α]
  simp

/-- Charge-like transported quantities `q I` have no localization correction. -/
@[simp]
theorem localizationCorrectionCurrentFlux_smul_id
    (velocity : V →ₗ[K] V)
    (N : OneForm →ₗ[K] (V →ₗ[K] V)) (q : K) :
    localizationCorrectionCurrentFlux V velocity (q • LinearMap.id) N = 0 := by
  apply localizationCorrectionCurrentFlux_eq_zero_of_commutes V velocity
    (q • LinearMap.id) N
  intro α
  simp [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]

end ConservationLaw
