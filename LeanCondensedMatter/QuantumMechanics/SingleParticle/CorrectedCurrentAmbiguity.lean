import LeanCondensedMatter.QuantumMechanics.SingleParticle.CorrectedCurrent

set_option linter.style.header false

/-!
# Extension ambiguity of the corrected current

This module states the general current result in the form most directly used in physics: every full
current functional representing the same intrinsic transport is the generic symmetrized flux plus
the canonical localization correction, up to a functional that vanishes on exact differentials.
-/

namespace QuantumMechanics
namespace SingleParticle

variable {Test OneForm : Type*}
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- Any representative of the same intrinsic transport has the form

`J = J_sym + J_corr + K`

with `K (d f) = 0` for every test object `f`. Thus `K` is pure extension ambiguity invisible
to the intrinsic flux. -/
theorem exists_current_eq_symmetrized_add_correction_add_invisible
    (ℏ : ℝ) (h : V →ₗ[ℂ] V)
    (M : Test →ₗ[ℂ] (V →ₗ[ℂ] V))
    (m velocity : V →ₗ[ℂ] V)
    (d : Test →ₗ[ℂ] OneForm)
    (N : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V))
    (hvelocity : heisenbergLocalizationFunctional V ℏ h M =
      (_root_.ConservationLaw.localizedQuantityFunctional N velocity).comp d)
    (R : _root_.ConservationLaw.DifferentialCurrentRepresentation d
      (heisenbergTransportFunctional V ℏ h M m)) :
    ∃ K : OneForm →ₗ[ℂ] (V →ₗ[ℂ] V),
      K.comp d = 0 ∧
        R.current =
          (_root_.ConservationLaw.symmetrizedCurrentFlux velocity m N +
            _root_.ConservationLaw.localizationCorrectionCurrentFlux velocity m N) + K := by
  refine ⟨R.current - _root_.ConservationLaw.nestedSymmetrizedCurrentFlux velocity m N,
    ?_, ?_⟩
  · rw [LinearMap.sub_comp,
      currentEquivalent_nestedSymmetrizedCurrentFlux V ℏ h M m velocity d N hvelocity R,
      sub_self]
  · rw [← _root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction,
      add_comm, sub_add_cancel]


end SingleParticle
end QuantumMechanics
