import LeanCondensedMatter.Analysis.ConservationLaw.CorrectedCurrentFlux
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.IntrinsicFluxResponse
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel

set_option linter.style.header false

/-!
# Corrected current response decomposition

This module lifts the analysis-level decomposition

```text
J_nested = J_sym + J_corr
J_corr(α) = 1/4 [v,[N α,m]]
```

to the bounded finite-lattice causal Kubo response.  It does not import first-quantized quantum
mechanics: `velocity`, `m`, and the operator-valued one-form localizer `N` are supplied one-body
operators/data.

When an intrinsic transport `Φ` factors through `J_nested ∘ d`, its exact-flux response decomposes
canonically into symmetrized and localization-correction responses. The same bounded corrected
current also defines a response channel with independent source and observable-variation inputs.
This remains a statement on exact differential data; no uniqueness of arbitrary/global current
extensions is claimed.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

attribute [local instance 100] LieRing.ofAssociativeRing

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

variable {Site Test OneForm : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup Test] [Module ℂ Test]
variable [AddCommGroup OneForm] [Module ℂ OneForm]

/-- Bounded Fock-space observable associated with one corrected/nested current component. -/
noncomputable def boundedCorrectedCurrentObservable
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedOneBodyOperator
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
      (LatticeState Site) velocity m N α)

/-- Response channel for one corrected current component.

The measured observable is the bounded corrected current. The source vertex and its explicit
observable variation are supplied independently, as needed for spin and orbital current response. -/
noncomputable def correctedCurrentResponseChannel
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (α : OneForm)
    (source observableVariation :
      FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :
    QuantumTheory.LinearResponse.ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedCorrectedCurrentObservable velocity m N α
  source := source
  observableVariation := observableVariation

/-- An intrinsic exact-flux response represented by the nested current decomposes into
symmetrized plus localization-correction responses. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_symmetrized_add_correction
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.IsDifferentialCurrent d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity m N))
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedIntrinsicFluxRetardedResponse system expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux
          (LatticeState Site) velocity m N) t s).comp d +
      (boundedIntrinsicFluxRetardedResponse system expectation source
        (_root_.ConservationLaw.localizationCorrectionCurrentFlux
          (LatticeState Site) velocity m N) t s).comp d := by
  apply LinearMap.ext
  intro f
  change
    (boundedOneBodyRetardedResponseLinearMap system expectation source t s) (Φ f) =
      (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
          (_root_.ConservationLaw.symmetrizedCurrentFlux
            (LatticeState Site) velocity m N (d f)) +
        (boundedOneBodyRetardedResponseLinearMap system expectation source t s)
          (_root_.ConservationLaw.localizationCorrectionCurrentFlux
            (LatticeState Site) velocity m N (d f))
  rw [hΦ f]
  have hdecomp := congrArg
    (fun J : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site) => J (d f))
    (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux_eq_symmetrized_add_correction
      (LatticeState Site) velocity m N)
  rw [hdecomp]
  exact map_add (boundedOneBodyRetardedResponseLinearMap system expectation source t s) _ _

/-- When all supplied localizers commute with `m`, the correction disappears and the intrinsic
exact-flux response is represented by the symmetrized current flux alone. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_symmetrized_of_commutes
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (source : FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)
    (d : Test →ₗ[ℂ] OneForm)
    (Φ : Test →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (velocity m : LatticeState Site →ₗ[ℂ] LatticeState Site)
    (N : OneForm →ₗ[ℂ] (LatticeState Site →ₗ[ℂ] LatticeState Site))
    (hΦ : _root_.ConservationLaw.IsDifferentialCurrent d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity m N))
    (hcomm : ∀ α, ⁅N α, m⁆ = 0)
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedIntrinsicFluxRetardedResponse system expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux
          (LatticeState Site) velocity m N) t s).comp d := by
  rw [boundedIntrinsicFluxRetardedResponse_eq_symmetrized_add_correction
    system expectation source d Φ velocity m N hΦ t s]
  have hcorr :
      _root_.ConservationLaw.localizationCorrectionCurrentFlux
        (LatticeState Site) velocity m N = 0 :=
    _root_.ConservationLaw.localizationCorrectionCurrentFlux_eq_zero_of_commutes
      (LatticeState Site) velocity m N hcomm
  rw [hcorr]
  simp [boundedIntrinsicFluxRetardedResponse]

/-- Charge-like quantities `m = q I` are a specialization of the commuting case: their correction
response vanishes identically on exact fluxes. -/
theorem boundedIntrinsicFluxRetardedResponse_eq_symmetrized_smul_id
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
    (hΦ : _root_.ConservationLaw.IsDifferentialCurrent d Φ
      (_root_.ConservationLaw.nestedSymmetrizedCurrentFlux
        (LatticeState Site) velocity (q • LinearMap.id) N))
    (t s : ℝ) :
    boundedIntrinsicFluxRetardedResponse system expectation source Φ t s =
      (boundedIntrinsicFluxRetardedResponse system expectation source
        (_root_.ConservationLaw.symmetrizedCurrentFlux
          (LatticeState Site) velocity (q • LinearMap.id) N) t s).comp d := by
  apply boundedIntrinsicFluxRetardedResponse_eq_symmetrized_of_commutes
    system expectation source d Φ velocity (q • LinearMap.id) N hΦ
  intro α
  simp [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp]

end
end Transport
end Fermionic
end SecondQuantization
