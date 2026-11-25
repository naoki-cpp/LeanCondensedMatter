import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct

set_option linter.style.header false

/-!
# Symmetric localization and corrected flux algebra

For a linear localization map `M` valued in an associative algebra and a transported quantity `m`,
symmetric localization is `Qₘ(f) = {M f, m}/2`. Commutation with a generator
splits into transport and source by `LinearMap.lie_symmetrizedProduct`.

For a one-form localizer `N` and a distinguished operator `v`, the nested flux
`{{N α, v}/2, m}/2` differs from the flux `{N α, {v,m}/2}/2` by
`[v,[N α,m]]/4`.

These are algebraic identities (with the usual physical interpretation when 2 is
nonzero). Neither a differential-current representation nor Heisenberg dynamics
is assumed; both are supplied downstream.
-/

namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K Test OneForm : Type*} [Field K]
variable [AddCommGroup Test] [Module K Test]
variable [AddCommGroup OneForm] [Module K OneForm]
variable {A : Type*} [Ring A] [Algebra K A]

/-- A quantity symmetrically localized by a linear test map. -/
noncomputable def localizedQuantityFunctional
    (M : Test →ₗ[K] A)
    (m : A) :
    Test →ₗ[K] A :=
  ((LinearMap.symmetrizedProductBilinear (K := K) A).flip m).comp M

@[simp]
theorem localizedQuantityFunctional_apply
    (M : Test →ₗ[K] A)
    (m : A) (f : Test) :
    localizedQuantityFunctional M m f = LinearMap.symmetrizedProduct (K := K) (M f) m :=
  rfl

section CorrectedFlux

/-- Full nested symmetrized flux on one-form-like localization data. -/
noncomputable def nestedSymmetrizedCurrentFlux
    (velocity m : A)
    (N : OneForm →ₗ[K] A) :
    OneForm →ₗ[K] A :=
  localizedQuantityFunctional (localizedQuantityFunctional N velocity) m

@[simp]
theorem nestedSymmetrizedCurrentFlux_apply
    (velocity m : A)
    (N : OneForm →ₗ[K] A) (α : OneForm) :
    nestedSymmetrizedCurrentFlux velocity m N α =
      LinearMap.symmetrizedProduct (K := K) (LinearMap.symmetrizedProduct (K := K) (N α) velocity) m :=
  rfl

/-- Flux obtained from the symmetrized current `1/2 {v,m}`. -/
noncomputable def symmetrizedCurrentFlux
    (velocity m : A)
    (N : OneForm →ₗ[K] A) :
    OneForm →ₗ[K] A :=
  localizedQuantityFunctional N (LinearMap.symmetrizedProduct (K := K) velocity m)

@[simp]
theorem symmetrizedCurrentFlux_apply
    (velocity m : A)
    (N : OneForm →ₗ[K] A) (α : OneForm) :
    symmetrizedCurrentFlux velocity m N α =
      LinearMap.symmetrizedProduct (K := K) (N α) (LinearMap.symmetrizedProduct (K := K) velocity m) :=
  rfl

/-- Canonical localization correction, defined as the exact difference between the nested and
symmetrized fluxes. -/
noncomputable def localizationCorrectionCurrentFlux
    (velocity m : A)
    (N : OneForm →ₗ[K] A) :
    OneForm →ₗ[K] A :=
  nestedSymmetrizedCurrentFlux velocity m N -
    symmetrizedCurrentFlux velocity m N

@[simp]
theorem localizationCorrectionCurrentFlux_apply
    (velocity m : A)
    (N : OneForm →ₗ[K] A) (α : OneForm) :
    localizationCorrectionCurrentFlux velocity m N α =
      (1 / 4 : K) • ⁅velocity, ⁅N α, m⁆⁆ := by
  change
    LinearMap.symmetrizedProduct (K := K) (LinearMap.symmetrizedProduct (K := K) (N α) velocity) m -
      LinearMap.symmetrizedProduct (K := K) (N α) (LinearMap.symmetrizedProduct (K := K) velocity m) = _
  rw [LinearMap.symmetrizedProduct_nested, add_comm, add_sub_cancel_right]

/-- The nested flux is exactly the symmetrized flux plus localization correction. -/
theorem nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction
    (velocity m : A)
    (N : OneForm →ₗ[K] A) :
    nestedSymmetrizedCurrentFlux velocity m N =
      symmetrizedCurrentFlux velocity m N +
        localizationCorrectionCurrentFlux velocity m N := by
  unfold localizationCorrectionCurrentFlux
  rw [add_comm, sub_add_cancel]

/-- If every supplied localizer commutes with `m`, the localization correction vanishes. -/
theorem localizationCorrectionCurrentFlux_eq_zero_of_commutes
    (velocity m : A)
    (N : OneForm →ₗ[K] A)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    localizationCorrectionCurrentFlux velocity m N = 0 := by
  apply LinearMap.ext
  intro α
  rw [localizationCorrectionCurrentFlux_apply velocity m N α, hcomm α]
  simp

/-- Scalar multiples of the algebra unit have no localization correction. -/
@[simp]
theorem localizationCorrectionCurrentFlux_smul_one
    (velocity : A)
    (N : OneForm →ₗ[K] A) (q : K) :
    localizationCorrectionCurrentFlux velocity (q • (1 : A)) N = 0 := by
  apply localizationCorrectionCurrentFlux_eq_zero_of_commutes velocity
    (q • (1 : A)) N
  intro α
  simp [LieRing.of_associative_ring_bracket, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

end CorrectedFlux

end ConservationLaw
