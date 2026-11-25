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
of that functional under additional assumptions. When localizer evolution admits a velocity
representation, the nested current flux represents intrinsic transport and differs from the
symmetrized flux by the canonical double-commutator correction. Full current extensions are
unique only on exact differential data.
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

section CorrectedCurrent

/-- A velocity representation of localizer evolution lifts to the generic nested current flux for
an arbitrary transported operator `m`; no locality/commutation assumption on `m` is needed. -/
theorem nestedSymmetrizedCurrentFlux_eq_comp
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d) :
    heisenbergTransportFunctional ℏ h M m =
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N).comp d := by
  calc
    heisenbergTransportFunctional ℏ h M m =
        _root_.ConservationLaw.localizedQuantityFunctional
          ((_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d) m :=
      congrArg (fun L : Test →ₗ[ℂ] 𝒜 =>
        _root_.ConservationLaw.localizedQuantityFunctional L m) hvelocity
    _ = _ := by
      apply LinearMap.ext
      intro f
      rfl

/-- The generic nested current flux is a chosen full differential-current representation of the
intrinsic transport whenever the localized Heisenberg evolution has a velocity representation. -/
noncomputable def correctedSymmetrizedVelocityCurrentRepresentation
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d) :
    _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional ℏ h M m) where
  val := _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N
  property := nestedSymmetrizedCurrentFlux_eq_comp ℏ h M m velocity d N hvelocity

/-- Any other full current functional representing the same intrinsic transport is equivalent on
exact differentials to the generic nested current flux. -/
theorem currentEquivalent_nestedSymmetrizedCurrentFlux
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional ℏ h M m)) :
    R.val.comp d =
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N).comp d :=
  R.property.symm.trans
    (correctedSymmetrizedVelocityCurrentRepresentation ℏ h M m velocity d N hvelocity).property

/-- Any representative of the same intrinsic transport has the form

`J = J_sym + J_corr + K`

with `K (d f) = 0` for every test object `f`. Thus `K` is pure extension ambiguity invisible
to the intrinsic flux. -/
theorem exists_current_eq_symmetrized_add_correction_add_invisible
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional ℏ h M m)) :
    ∃ K : OneForm →ₗ[ℂ] 𝒜,
      K.comp d = 0 ∧
        R.val =
          (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N +
            _root_.ConservationLaw.localizationCorrectionCurrentFlux velocity m N) + K := by
  refine ⟨R.val - _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N,
    ?_, ?_⟩
  · rw [LinearMap.sub_comp,
      currentEquivalent_nestedSymmetrizedCurrentFlux ℏ h M m velocity d N hvelocity R,
      sub_self]
  · rw [← _root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      add_comm, sub_add_cancel]

/-- The symmetrized velocity current supplies a local current-density representation whenever the
Heisenberg localization transport is first-order in `d` and the localized one-form operators
commute with the transported quantity. -/
noncomputable def symmetrizedVelocityCurrentRepresentation
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      d
      (heisenbergTransportFunctional ℏ h M m)
      (operatorLocalCurrentPairing N) where
  val := _root_.LinearMap.symmetrizedProduct (K := ℂ) velocity m
  property := by
    change heisenbergTransportFunctional ℏ h M m =
      (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N).comp d
    rw [nestedSymmetrizedCurrentFlux_eq_comp ℏ h M m velocity d N hvelocity,
      _root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      _root_.ConservationLaw.localizationCorrectionCurrentFlux_eq_zero_of_commutes
        velocity m N hcomm, add_zero]

@[simp]
theorem symmetrizedVelocityCurrentRepresentation_currentDensity
    (ℏ : ℝ) (h : 𝒜)
    (M : Test →ₗ[ℂ] 𝒜)
    (m velocity : 𝒜)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] 𝒜)
    (hvelocity : heisenbergLocalizationFunctional ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (hcomm : ∀ α, ⁅N α, m⁆ = 0) :
    (symmetrizedVelocityCurrentRepresentation ℏ h M m velocity d N hvelocity hcomm).val =
      _root_.LinearMap.symmetrizedProduct (K := ℂ) velocity m :=
  rfl

/-- The canonical corrected flux for a scalar quantity `q • 1` is the local pairing
with charge-current density `q • velocity`. -/
theorem correctedChargeCurrentFlux_eq
    (velocity : 𝒜) (N : OneForm →ₗ[ℂ] 𝒜) (q : ℂ) :
    _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity (q • 1) N =
      operatorLocalCurrentPairing N (q • velocity) := by
  rw [_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
    _root_.ConservationLaw.localizationCorrectionCurrentFlux_smul_one velocity N q, add_zero]
  apply LinearMap.ext
  intro α
  rw [_root_.ConservationLaw.symmetrizedCurrentFlux_apply,
    operatorLocalCurrentPairing_apply, _root_.LinearMap.symmetrizedProduct_smul_one]

end CorrectedCurrent

end ConservationLaw
end QuantumTheory
