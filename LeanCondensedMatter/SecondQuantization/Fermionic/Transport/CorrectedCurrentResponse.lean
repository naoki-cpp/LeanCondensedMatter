import LeanCondensedMatter.Analysis.Calculus.CorrectedCurrentFlux
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.IntrinsicFluxResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConventionalCurrentResponse

set_option linter.style.header false

/-!
# Corrected current response decomposition

This module lifts the analysis-level decomposition

```text
J_nested = J_conv + J_corr
J_corr(α) = 1/4 [v,[N α,m]]
```

to the bounded finite-lattice causal Kubo response.  It does not import first-quantized quantum
mechanics: `velocity`, `m`, and the operator-valued one-form localizer `N` are supplied one-body
operators/data.

When an intrinsic transport `Φ` factors through `J_nested ∘ d`, its exact-flux response decomposes
canonically into conventional/symmetrized and localization-correction responses.  This remains a
statement on exact differential data; no uniqueness of arbitrary/global current extensions is
claimed.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site Test OneForm : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- Retarded response of the conventional/symmetrized current flux
`α ↦ 1/2 {N α, 1/2 {v,m}}`. -/
noncomputable def boundedConventionalCurrentFluxRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) : OneForm →ₗ[ℂ] ℂ :=
  boundedCurrentFunctionalRetardedResponse system expectation source
    (_root_.ConservationLaw.conventionalSymmetrizedCurrentFlux
      (LatticeState Site) velocity m N) t s

/-- Retarded response of the canonical localization correction
`α ↦ 1/4 [v,[N α,m]]`. -/
noncomputable def boundedLocalizationCorrectionRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) : OneForm →ₗ[ℂ] ℂ :=
  boundedCurrentFunctionalRetardedResponse system expectation source
    (_root_.ConservationLaw.localizationCorrectionCurrentFlux
      (LatticeState Site) velocity m N) t s

/-- Retarded response of the full nested/corrected current functional. -/
noncomputable def boundedCorrectedCurrentFluxRetardedResponse
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) : OneForm →ₗ[ℂ] ℂ :=
  boundedCurrentFunctionalRetardedResponse system expectation source
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
      (LatticeState Site) velocity m N) t s

/-- Kubo linearity lifts the corrected-current decomposition pointwise on one-form data. -/
theorem boundedCorrectedCurrentFluxRetardedResponse_eq_conventional_add_correction
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (t s : ℝ) :
    boundedCorrectedCurrentFluxRetardedResponse system expectation source velocity m N t s =
      boundedConventionalCurrentFluxRetardedResponse system expectation source velocity m N t s +
        boundedLocalizationCorrectionRetardedResponse system expectation source velocity m N t s := by
  apply LinearMap.ext
  intro α
  change
    (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
        (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
          (LatticeState Site) velocity m N α) =
      (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
          (_root_.ConservationLaw.conventionalSymmetrizedCurrentFlux
            (LatticeState Site) velocity m N α) +
        (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
          (_root_.ConservationLaw.localizationCorrectionCurrentFlux
            (LatticeState Site) velocity m N α)
  have hdecomp := congrArg
    (fun J : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site) => J α)
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_conventional_add_correction
      (LatticeState Site) velocity m N)
  rw [hdecomp]
  exact map_add (boundedOneBodyRetardedResponseLinearMap system expectation source t s) _ _

/-- If `Φ` is represented by the nested/corrected current on exact differentials, its intrinsic
Kubo response is exactly the corrected-current response precomposed with `d`. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_corrected_of_factors
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.FactorsThroughDifferential d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity m N))
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedCorrectedCurrentFluxRetardedResponse
        system expectation source velocity m N t s).comp d := by
  apply LinearMap.ext
  intro f
  change
    (boundedOneBodyRetardedResponseLinearMap system expectation source t s) (Φ f) =
      (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
        (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
          (LatticeState Site) velocity m N (d f))
  rw [hΦ f]

/-- Fundamental Phase-2 response theorem: an intrinsic exact-flux response represented by the
nested current decomposes into conventional/symmetrized plus localization-correction responses. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_conventional_add_correction
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.FactorsThroughDifferential d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity m N))
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedConventionalCurrentFluxRetardedResponse
        system expectation source velocity m N t s).comp d +
      (boundedLocalizationCorrectionRetardedResponse
        system expectation source velocity m N t s).comp d := by
  rw [boundedIntrinsicFluxRetardedResponse_eq_corrected_of_factors
    system expectation source d Φ velocity m N hΦ t s]
  rw [boundedCorrectedCurrentFluxRetardedResponse_eq_conventional_add_correction
    system expectation source velocity m N t s]
  apply LinearMap.ext
  intro f
  rfl

/-- When all supplied localizers commute with `m`, the correction disappears and the intrinsic
exact-flux response is represented by the conventional/symmetrized current flux alone. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_conventional_of_commutes
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.FactorsThroughDifferential d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity m N))
    (hcomm : ∀ α, _root_.ConservationLaw.linearCommutator (N α) m = 0)
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedConventionalCurrentFluxRetardedResponse
        system expectation source velocity m N t s).comp d := by
  rw [boundedIntrinsicFluxRetardedResponse_eq_conventional_add_correction
    system expectation source d Φ velocity m N hΦ t s]
  have hcorr :
      boundedLocalizationCorrectionRetardedResponse
        system expectation source velocity m N t s = 0 := by
    apply LinearMap.ext
    intro α
    change
      (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
        (_root_.ConservationLaw.localizationCorrectionCurrentFlux
          (LatticeState Site) velocity m N α) = 0
    rw [_root_.ConservationLaw.localizationCorrectionCurrentFlux_eq_zero_of_commutes
      (LatticeState Site) velocity m N hcomm]
    simp
  rw [hcorr]
  simp

/-- Charge-like quantities `m = q I` are a specialization of the commuting case: their correction
response vanishes identically on exact fluxes. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_conventional_smul_id
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (q : ℂ)
    (hΦ : _root_.ConservationLaw.FactorsThroughDifferential d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity (q • LinearMap.id) N))
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedConventionalCurrentFluxRetardedResponse
        system expectation source velocity (q • LinearMap.id) N t s).comp d := by
  apply boundedIntrinsicFluxRetardedResponse_eq_conventional_of_commutes
    system expectation source d Φ velocity (q • LinearMap.id) N hΦ
  intro α
  exact _root_.ConservationLaw.linearCommutator_smul_id_right (N α) q

end
end Transport
end Fermionic
end SecondQuantization
