import LeanCondensedMatter.Analysis.Operator.SchwartzTwoLevel1D
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent

set_option linter.style.header false

/-!
# Spin-current representation on one-dimensional Schwartz spinors

This module realizes the internal-spin specialization requested by #1159. The one-particle space is
the two-component Schwartz spinor model from `Analysis.Operator.SchwartzTwoLevel1D`. Spatial
localization and velocity act componentwise, while `S(n) = ℏ (n · σ) / 2` acts only on the internal
`Fin 2` index.

Consequently localization commutes with spin, so the generalized transport functional has the
symmetrized velocity-current representation

```text
j^(S(n)) = 1/2 {v, S(n)}.
```

This operator is often called the conventional spin current in the physics literature (see Shi,
Zhang, Xiao, and Niu, *Phys. Rev. Lett.* **96**, 076604 (2006),
[doi:10.1103/PhysRevLett.96.076604](https://doi.org/10.1103/PhysRevLett.96.076604)), but the
transport functional is the primary object here. In this spinor model `v` also commutes with
`S(n)`, hence the chosen current density simplifies further to `v S(n)`. An arbitrary internal
Hamiltonian matrix is retained; its commutator with `S(n)` supplies the local source/torque term.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

open QuantumTheory.ConservationLaw

noncomputable section

/-- Concrete two-component Schwartz one-particle space. -/
abbrev SchwartzSpinorOneParticle1D := SchwartzTwoLevel1D.Spinor

/-- Spin-1/2 operator associated with a three-dimensional spin-space component vector. -/
noncomputable def schwartzSpinOperator
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    SchwartzSpinorOneParticle1D →ₗ[ℂ] SchwartzSpinorOneParticle1D :=
  SchwartzTwoLevel1D.internalOperator (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)

/-- The componentwise velocity-generated flux is a differential current for the spinor Schrödinger
localization transport. -/
theorem schwartzSpinorVelocityLocalizationFlux_isDifferentialCurrent1D
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) :
    _root_.ConservationLaw.IsDifferentialCurrent
      SchwartzTwoLevel1D.derivative
      (heisenbergLocalizationFunctional SchwartzSpinorOneParticle1D ℏ
        (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear)
      (velocityLocalizationFlux SchwartzSpinorOneParticle1D
        (SchwartzTwoLevel1D.velocityOperator ℏ κ)
        SchwartzTwoLevel1D.multiplicationLinear) := by
  intro f
  simpa [heisenbergLocalizationFunctional, heisenbergScale,
    localizationCommutatorFunctional, _root_.ConservationLaw.linearCommutator,
    velocityLocalizationFlux, symmetrizedProductRightLinear,
    _root_.ConservationLaw.symmetrizedProduct] using
    (SchwartzTwoLevel1D.heisenberg_localization_eq_symmetrized_velocity
      ℏ κ potential internalH f)

/-- Multiplication localization commutes with a concrete spin component. -/
theorem schwartzSpin_localization_commutator_eq_zero
    (f : SchwartzTwoLevel1D.Spatial) (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    _root_.ConservationLaw.linearCommutator
      (SchwartzTwoLevel1D.multiplicationOperator f)
      (schwartzSpinOperator ℏ spinComponent) = 0 := by
  exact sub_eq_zero.mpr
    (SchwartzTwoLevel1D.spatialLift_comp_internalOperator_comm
      (SchwartzKinetic1D.multiplicationOperator f)
      (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent))

/-- The symmetrized velocity-current representation of spin transport on the Schwartz model. -/
noncomputable def schwartzSpinCurrentRepresentation1D
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      SchwartzTwoLevel1D.derivative
      (heisenbergTransportFunctional SchwartzSpinorOneParticle1D ℏ
        (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperator ℏ spinComponent))
      (operatorLocalCurrentPairing SchwartzSpinorOneParticle1D
        SchwartzTwoLevel1D.multiplicationLinear) :=
  symmetrizedVelocityCurrentRepresentation SchwartzSpinorOneParticle1D ℏ
    (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
    SchwartzTwoLevel1D.multiplicationLinear
    (schwartzSpinOperator ℏ spinComponent)
    (SchwartzTwoLevel1D.velocityOperator ℏ κ)
    SchwartzTwoLevel1D.derivative
    SchwartzTwoLevel1D.multiplicationLinear
    (schwartzSpinorVelocityLocalizationFlux_isDifferentialCurrent1D
      ℏ κ potential internalH)
    (fun α => schwartzSpin_localization_commutator_eq_zero α ℏ spinComponent)

@[simp]
theorem schwartzSpinCurrentRepresentation1D_currentDensity
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    (schwartzSpinCurrentRepresentation1D ℏ κ potential internalH spinComponent).currentDensity =
      symmetrizedVelocityCurrent SchwartzSpinorOneParticle1D
        (SchwartzTwoLevel1D.velocityOperator ℏ κ)
        (schwartzSpinOperator ℏ spinComponent) :=
  rfl

/-- In the internal-spin model the velocity and spin operators commute. -/
theorem schwartzSpin_velocity_commutator_eq_zero
    (ℏ κ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    _root_.ConservationLaw.linearCommutator
      (SchwartzTwoLevel1D.velocityOperator ℏ κ)
      (schwartzSpinOperator ℏ spinComponent) = 0 := by
  exact sub_eq_zero.mpr
    (SchwartzTwoLevel1D.spatialLift_comp_internalOperator_comm
      (SchwartzKinetic1D.velocityOperator ℏ κ)
      (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent))

/-- The symmetrized spin current simplifies from `1/2 {v,S(n)}` to `v S(n)`. -/
theorem symmetrizedSpinCurrent_eq_velocity_comp_spin
    (ℏ κ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    symmetrizedVelocityCurrent SchwartzSpinorOneParticle1D
        (SchwartzTwoLevel1D.velocityOperator ℏ κ)
        (schwartzSpinOperator ℏ spinComponent) =
      (SchwartzTwoLevel1D.velocityOperator ℏ κ).comp
        (schwartzSpinOperator ℏ spinComponent) := by
  exact _root_.ConservationLaw.symmetrizedProduct_eq_comp_of_commutes
    (SchwartzTwoLevel1D.velocityOperator ℏ κ)
    (schwartzSpinOperator ℏ spinComponent)
    (schwartzSpin_velocity_commutator_eq_zero ℏ κ spinComponent)

/-- The current density stored in the local representation is exactly `v S(n)`. -/
theorem schwartzSpinCurrentRepresentation1D_currentDensity_eq_velocity_comp_spin
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    (schwartzSpinCurrentRepresentation1D ℏ κ potential internalH spinComponent).currentDensity =
      (SchwartzTwoLevel1D.velocityOperator ℏ κ).comp
        (schwartzSpinOperator ℏ spinComponent) := by
  rw [schwartzSpinCurrentRepresentation1D_currentDensity]
  exact symmetrizedSpinCurrent_eq_velocity_comp_spin ℏ κ spinComponent

/-- The spin commutator of the full Hamiltonian is entirely the commutator with the internal
Hamiltonian matrix. -/
theorem linearCommutator_schwartzSpinorHamiltonian_spinAlong
    (κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix)
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    _root_.ConservationLaw.linearCommutator
        (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
        (schwartzSpinOperator ℏ spinComponent) =
      _root_.ConservationLaw.linearCommutator
        (SchwartzTwoLevel1D.internalOperator internalH)
        (schwartzSpinOperator ℏ spinComponent) := by
  exact SchwartzTwoLevel1D.hamiltonian_internalOperator_commutator_eq_internal
    κ potential internalH (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)

/-- The canonical localized spin source/torque is generated only by the internal Hamiltonian
commutator `[H_internal,S(n)]`. -/
theorem schwartzSpin_sourceCommutator_eq_internal
    (κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix)
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) (f : SchwartzTwoLevel1D.Spatial) :
    _root_.ConservationLaw.sourceCommutator SchwartzSpinorOneParticle1D
        (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperator ℏ spinComponent) f =
      _root_.ConservationLaw.symmetrizedProduct
        (SchwartzTwoLevel1D.multiplicationOperator f)
        (_root_.ConservationLaw.linearCommutator
          (SchwartzTwoLevel1D.internalOperator internalH)
          (schwartzSpinOperator ℏ spinComponent)) := by
  rw [_root_.ConservationLaw.sourceCommutator]
  rw [linearCommutator_schwartzSpinorHamiltonian_spinAlong]
  rfl

/-- If the internal Hamiltonian conserves the selected spin component, the local spin source
vanishes and the balance law reduces to pure transport. -/
theorem schwartzSpin_sourceCommutator_eq_zero_of_internal_commutes
    (κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix)
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) (f : SchwartzTwoLevel1D.Spatial)
    (hcomm : _root_.ConservationLaw.linearCommutator
      (SchwartzTwoLevel1D.internalOperator internalH)
      (schwartzSpinOperator ℏ spinComponent) = 0) :
    _root_.ConservationLaw.sourceCommutator SchwartzSpinorOneParticle1D
        (SchwartzTwoLevel1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperator ℏ spinComponent) f = 0 := by
  rw [schwartzSpin_sourceCommutator_eq_internal]
  simp [hcomm]

end
end Continuum
end SingleParticle
end QuantumMechanics
