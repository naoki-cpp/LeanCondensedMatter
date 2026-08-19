import LeanCondensedMatter.Analysis.Calculus.SymmetricLocalization
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Corrected symmetrized-current flux algebra

This module packages the pure operator algebra behind the decomposition of a nested localized
transport into a conventional/symmetrized current contribution and a localization correction.
No Heisenberg dynamics, first-quantized velocity semantics, second quantization, or response theory
is assumed here.

For an operator-valued one-form localizer `N`, a distinguished operator `v`, and transported
quantity `m`, define

```text
J_nested(α) = 1/2 { 1/2 {N α, v}, m }
J_conv(α)   = 1/2 { N α, 1/2 {v,m} }
J_corr      = J_nested - J_conv.
```

Then

```text
J_corr(α) = 1/4 [v,[N α,m]].
```

These are current-functionals on supplied one-form-like data.  Whether they represent an intrinsic
transport through a differential is a separate downstream statement.
-/

namespace ConservationLaw

variable {OneForm : Type*}
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Full nested symmetrized flux on one-form-like localization data. -/
noncomputable def nestedSymmetrizedCurrentFlux
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    OneForm →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (symmetrizedProductRightLinear V m).comp
    ((symmetrizedProductRightLinear V velocity).comp N)

@[simp]
theorem nestedSymmetrizedCurrentFlux_apply
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) (α : OneForm) :
    nestedSymmetrizedCurrentFlux V velocity m N α =
      symmetrizedProduct (symmetrizedProduct (N α) velocity) m :=
  rfl

/-- Flux obtained from the conventional/symmetrized current `1/2 {v,m}`. -/
noncomputable def conventionalSymmetrizedCurrentFlux
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    OneForm →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  (symmetrizedProductRightLinear V (symmetrizedProduct velocity m)).comp N

@[simp]
theorem conventionalSymmetrizedCurrentFlux_apply
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) (α : OneForm) :
    conventionalSymmetrizedCurrentFlux V velocity m N α =
      symmetrizedProduct (N α) (symmetrizedProduct velocity m) :=
  rfl

/-- Canonical localization correction, defined as the exact difference between nested and
conventional/symmetrized fluxes. -/
noncomputable def localizationCorrectionCurrentFlux
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    OneForm →ₗ[ℂ] (V →ₗ[ℂ] V) :=
  nestedSymmetrizedCurrentFlux V velocity m N -
    conventionalSymmetrizedCurrentFlux V velocity m N

@[simp]
theorem localizationCorrectionCurrentFlux_apply
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) (α : OneForm) :
    localizationCorrectionCurrentFlux V velocity m N α =
      (1 / 4 : ℂ) • linearCommutator velocity (linearCommutator (N α) m) := by
  change
    symmetrizedProduct (symmetrizedProduct (N α) velocity) m -
      symmetrizedProduct (N α) (symmetrizedProduct velocity m) = _
  rw [symmetrizedProduct_nested]
  module

/-- The nested flux is exactly conventional/symmetrized flux plus localization correction. -/
theorem nestedSymmetrizedCurrentFlux_eq_conventional_add_correction
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) :
    nestedSymmetrizedCurrentFlux V velocity m N =
      conventionalSymmetrizedCurrentFlux V velocity m N +
        localizationCorrectionCurrentFlux V velocity m N := by
  unfold localizationCorrectionCurrentFlux
  module

/-- If every supplied localizer commutes with `m`, the localization correction vanishes. -/
theorem localizationCorrectionCurrentFlux_eq_zero_of_commutes
    (velocity m : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hcomm : ∀ α, linearCommutator (N α) m = 0) :
    localizationCorrectionCurrentFlux V velocity m N = 0 := by
  apply LinearMap.ext
  intro α
  rw [localizationCorrectionCurrentFlux_apply V velocity m N α, hcomm α]
  simp [linearCommutator]

/-- Charge-like transported quantities `q I` have no localization correction. -/
@[simp]
theorem localizationCorrectionCurrentFlux_smul_id
    (velocity : V →ₗ[ℂ] V)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V)) (q : ℂ) :
    localizationCorrectionCurrentFlux V velocity (q • LinearMap.id) N = 0 := by
  apply localizationCorrectionCurrentFlux_eq_zero_of_commutes V velocity
    (q • LinearMap.id) N
  intro α
  exact linearCommutator_smul_id_right (N α) q

end ConservationLaw
