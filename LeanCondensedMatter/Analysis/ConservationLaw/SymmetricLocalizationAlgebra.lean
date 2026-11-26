import LeanCondensedMatter.Analysis.Operator.SymmetrizedProduct
import LeanCondensedMatter.Analysis.ConservationLaw.CurrentRepresentation

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
nonzero). The same algebra constructs current representations from any supplied linear
localizer evolution with a velocity representation; no Heisenberg dynamics is assumed.
-/

namespace ConservationLaw

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K Test OneForm : Type*} [Field K]
variable [AddCommGroup Test] [Module K Test]
variable [AddCommGroup OneForm] [Module K OneForm]
variable {A : Type*} [Ring A] [Algebra K A]

/-- Symmetric localization, bundled linearly in the transported quantity as well as the test.
For a one-form localizer this is also the local current-density pairing. -/
noncomputable def localizedQuantityFunctional
    (M : Test →ₗ[K] A) :
    A →ₗ[K] (Test →ₗ[K] A) :=
  ((LinearMap.llcomp K Test A A).flip M).comp
    (LinearMap.symmetrizedProductBilinear (K := K) A).flip

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

section CorrectedCurrent

/-- A velocity representation of localizer evolution lifts to the generic nested current flux for
an arbitrary transported operator `m`; no locality/commutation assumption on `m` is needed. -/
theorem nestedSymmetrizedCurrentFlux_eq_comp
    (L : Test →ₗ[K] A)
    (m velocity : A)
    (d : Test →ₗ[K] OneForm)
    (N : OneForm →ₗ[K] A)
    (hvelocity : L =
      (localizedQuantityFunctional N velocity).comp d) :
    localizedQuantityFunctional L m =
      (nestedSymmetrizedCurrentFlux velocity m N).comp d := by
  calc
    localizedQuantityFunctional L m =
        localizedQuantityFunctional
          ((localizedQuantityFunctional N velocity).comp d) m :=
      congrArg (fun T : Test →ₗ[K] A => localizedQuantityFunctional T m) hvelocity
    _ = _ := by
      apply LinearMap.ext
      intro f
      rfl

/-- Any other full current functional representing the same intrinsic transport is equivalent on
exact differentials to the generic nested current flux. -/
theorem currentEquivalent_nestedSymmetrizedCurrentFlux
    (L : Test →ₗ[K] A)
    (m velocity : A)
    (d : Test →ₗ[K] OneForm)
    (N : OneForm →ₗ[K] A)
    (hvelocity : L =
      (localizedQuantityFunctional N velocity).comp d)
    (R : DifferentialCurrentRepresentation d
      (localizedQuantityFunctional L m)) :
    R.val.comp d =
      (nestedSymmetrizedCurrentFlux velocity m N).comp d :=
  R.property.symm.trans (nestedSymmetrizedCurrentFlux_eq_comp L m velocity d N hvelocity)

/-- Any representative of the same intrinsic transport has the form

`J = J_sym + J_corr + K`

with `K (d f) = 0` for every test object `f`. Thus `K` is pure extension ambiguity invisible
to the intrinsic flux. -/
theorem exists_current_eq_symmetrized_add_correction_add_invisible
    (L : Test →ₗ[K] A)
    (m velocity : A)
    (d : Test →ₗ[K] OneForm)
    (N : OneForm →ₗ[K] A)
    (hvelocity : L =
      (localizedQuantityFunctional N velocity).comp d)
    (R : DifferentialCurrentRepresentation d
      (localizedQuantityFunctional L m)) :
    ∃ K : OneForm →ₗ[K] A,
      K.comp d = 0 ∧
        R.val =
          (symmetrizedCurrentFlux velocity m N +
            localizationCorrectionCurrentFlux velocity m N) + K := by
  refine ⟨R.val - nestedSymmetrizedCurrentFlux velocity m N,
    ?_, ?_⟩
  · rw [LinearMap.sub_comp,
      currentEquivalent_nestedSymmetrizedCurrentFlux L m velocity d N hvelocity R,
      sub_self]
  · rw [← nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      add_comm, sub_add_cancel]

/-- The symmetrized velocity current supplies a local current-density representation whenever the
supplied localizer evolution factors through `d` and the localized one-form operators
commute with the transported quantity. -/
noncomputable def symmetrizedVelocityCurrentRepresentation
    (L : Test →ₗ[K] A)
    (m velocity : A)
    (d : Test →ₗ[K] OneForm)
    (N : OneForm →ₗ[K] A)
    (hvelocity : L =
      (localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    LocalCurrentDensityRepresentation
      d
      (localizedQuantityFunctional L m)
      (localizedQuantityFunctional N) where
  val := LinearMap.symmetrizedProduct (K := K) velocity m
  property := by
    change localizedQuantityFunctional L m =
      (symmetrizedCurrentFlux velocity m N).comp d
    rw [nestedSymmetrizedCurrentFlux_eq_comp L m velocity d N hvelocity,
      nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      localizationCorrectionCurrentFlux_eq_zero_of_commutes
        velocity m N hcomm, add_zero]

@[simp]
theorem symmetrizedVelocityCurrentRepresentation_currentDensity
    (L : Test →ₗ[K] A)
    (m velocity : A)
    (d : Test →ₗ[K] OneForm)
    (N : OneForm →ₗ[K] A)
    (hvelocity : L =
      (localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    (symmetrizedVelocityCurrentRepresentation L m velocity d N hvelocity hcomm).val =
      LinearMap.symmetrizedProduct (K := K) velocity m :=
  rfl

/-- The canonical corrected flux for a scalar quantity `q • 1` is the local pairing
with charge-current density `q • velocity`. -/
theorem correctedChargeCurrentFlux_eq [NeZero (2 : K)]
    (velocity : A) (N : OneForm →ₗ[K] A) (q : K) :
    nestedSymmetrizedCurrentFlux velocity (q • 1) N =
      localizedQuantityFunctional N (q • velocity) := by
  rw [nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
    localizationCorrectionCurrentFlux_smul_one velocity N q, add_zero,
    symmetrizedCurrentFlux, LinearMap.symmetrizedProduct_smul_one]

end CorrectedCurrent

end ConservationLaw
