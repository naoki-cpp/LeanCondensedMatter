import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct

set_option linter.style.header false

/-!
# Symmetric localization and corrected flux algebra

For an operator-valued linear localization map `M` and a transported quantity `m`,
symmetric localization is `Qₘ(f) = {M f, m}/2`. Commutation with a generator
splits into transport and source.

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
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- A one-body quantity symmetrically localized by a linear test map. -/
noncomputable def localizedQuantityFunctional
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  ((LinearMap.symmetrizedProductBilinear (K := K) (V →ₗ[K] V)).flip m).comp M

@[simp]
theorem localizedQuantityFunctional_apply
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    localizedQuantityFunctional V M m f = LinearMap.symmetrizedProduct (K := K) (M f) m :=
  rfl

/-- The bare localization commutator as a linear map on tests. -/
noncomputable def localizationCommutatorFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V)) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  (LieAlgebra.ad K (Module.End K V) h).comp M

@[simp]
theorem localizationCommutatorFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V)) (f : Test) :
    localizationCommutatorFunctional V h M f = ⁅h, M f⁆ :=
  rfl

/-- The transport contribution to the symmetric-localization commutator. -/
noncomputable def transportFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  localizedQuantityFunctional V (localizationCommutatorFunctional V h M) m

@[simp]
theorem transportFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    transportFunctional V h M m f = LinearMap.symmetrizedProduct (K := K) ⁅h, M f⁆ m :=
  rfl

/-- The source/torque contribution to the symmetric-localization commutator. -/
noncomputable def sourceFunctional
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) :
    Test →ₗ[K] (V →ₗ[K] V) :=
  localizedQuantityFunctional V M ⁅h, m⁆

@[simp]
theorem sourceFunctional_apply
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    sourceFunctional V h M m f = LinearMap.symmetrizedProduct (K := K) (M f) ⁅h, m⁆ :=
  rfl

/-- The commutator is a derivation on symmetric localization, giving transport plus source. -/
theorem lie_localizedQuantity
    (h : V →ₗ[K] V)
    (M : Test →ₗ[K] (V →ₗ[K] V))
    (m : V →ₗ[K] V) (f : Test) :
    ⁅h, localizedQuantityFunctional V M m f⁆ =
      transportFunctional V h M m f + sourceFunctional V h M m f :=
  LinearMap.lie_symmetrizedProduct (K := K) h (M f) m

section CorrectedFlux

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

end CorrectedFlux

end ConservationLaw
