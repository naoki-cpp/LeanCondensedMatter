import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchwartzTwoLevelSchrodinger1D
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumMechanics.SingleParticle.SymmetrizedVelocityCurrent

set_option linter.style.header false

/-!
# Spin-current representation on one-dimensional Schwartz spinors

This module realizes the internal-spin specialization requested by #1159. The one-particle space is
the two-level Schwartz model from `Analysis.Operator.SchwartzTwoLevel1D`, specialized here to
spin-1/2. Spatial
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

attribute [local instance 100] LieRing.ofAssociativeRing

open QuantumTheory.ConservationLaw

noncomputable section

/-- Concrete two-component Schwartz one-particle space. -/
abbrev SchwartzSpinorOneParticle1D := SchwartzTwoLevel1D.State

/-- Spin-1/2 operator as a real-linear function of the spin-space component vector. -/
noncomputable def schwartzSpinOperatorLinear
    (ℏ : ℝ) :
    QuantumTheory.SpinHalf.SpinSpace →ₗ[ℝ]
      (SchwartzSpinorOneParticle1D →ₗ[ℂ] SchwartzSpinorOneParticle1D) :=
  (SchwartzTwoLevel1D.internalOperatorLinear.restrictScalars ℝ).comp
    (QuantumTheory.SpinHalf.spinMatrix ℏ)

/-- With velocity fixed, the one-particle symmetrized spin-current density is real-linear in the
spin-space component vector. -/
noncomputable def schwartzSpinCurrentDensityLinear1D
    (ℏ κ : ℝ) :
    QuantumTheory.SpinHalf.SpinSpace →ₗ[ℝ]
      (SchwartzSpinorOneParticle1D →ₗ[ℂ] SchwartzSpinorOneParticle1D) :=
  ((symmetrizedVelocityCurrentLinear SchwartzSpinorOneParticle1D
      (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ)).restrictScalars ℝ).comp
    (schwartzSpinOperatorLinear ℏ)

@[simp]
theorem schwartzSpinCurrentDensityLinear1D_apply
    (ℏ κ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    schwartzSpinCurrentDensityLinear1D ℏ κ spinComponent =
      symmetrizedVelocityCurrent SchwartzSpinorOneParticle1D
        (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ)
        (schwartzSpinOperatorLinear ℏ spinComponent) :=
  rfl

/-- The componentwise velocity-generated flux is a differential current for the spinor Schrödinger
localization transport. -/
theorem schwartzSpinorVelocityLocalizationFlux_eq_comp1D
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) :
    (heisenbergLocalizationFunctional SchwartzSpinorOneParticle1D ℏ
        (SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear) =
      (velocityLocalizationFlux SchwartzSpinorOneParticle1D
        (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ)
        SchwartzTwoLevel1D.multiplicationLinear).comp SchwartzKinetic1D.derivative := by
  apply LinearMap.ext
  intro f
  rw [heisenbergLocalizationFunctional_apply]
  simp only [LinearMap.comp_apply, velocityLocalizationFlux_apply]
  apply LinearMap.ext
  intro ψ
  have h := congrArg
    (fun T : SchwartzSpinorOneParticle1D →ₗ[ℂ] SchwartzSpinorOneParticle1D => T ψ)
    (SchwartzTwoLevelSchrodinger1D.heisenberg_localization_eq_symmetrized_velocity
      ℏ κ potential internalH f)
  simpa [heisenbergScale, _root_.ConservationLaw.symmetrizedProduct_apply] using h

/-- The symmetrized velocity-current representation of spin transport on the Schwartz model. -/
noncomputable def schwartzSpinCurrentRepresentation1D
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    _root_.ConservationLaw.LocalCurrentDensityRepresentation
      SchwartzKinetic1D.derivative
      (heisenbergTransportFunctional SchwartzSpinorOneParticle1D ℏ
        (SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperatorLinear ℏ spinComponent))
      (operatorLocalCurrentPairing SchwartzSpinorOneParticle1D
        SchwartzTwoLevel1D.multiplicationLinear) :=
  symmetrizedVelocityCurrentRepresentation SchwartzSpinorOneParticle1D ℏ
    (SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH)
    SchwartzTwoLevel1D.multiplicationLinear
    (schwartzSpinOperatorLinear ℏ spinComponent)
    (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ)
    SchwartzKinetic1D.derivative
    SchwartzTwoLevel1D.multiplicationLinear
    (schwartzSpinorVelocityLocalizationFlux_eq_comp1D
      ℏ κ potential internalH)
    (fun α => by
      change
        ⁅SchwartzTwoLevel1D.spatialLift (SchwartzKinetic1D.multiplicationOperator α),
          SchwartzTwoLevel1D.internalOperator
            (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)⁆ = 0
      exact SchwartzTwoLevel1D.lie_spatialLift_internalOperator_eq_zero
        (SchwartzKinetic1D.multiplicationOperator α)
        (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent))

@[simp]
theorem schwartzSpinCurrentRepresentation1D_currentDensity
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    (schwartzSpinCurrentRepresentation1D ℏ κ potential internalH spinComponent).currentDensity =
      schwartzSpinCurrentDensityLinear1D ℏ κ spinComponent :=
  rfl

/-- The symmetrized spin current simplifies from `1/2 {v,S(n)}` to `v S(n)`. -/
theorem symmetrizedSpinCurrent_eq_velocity_comp_spin
    (ℏ κ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    symmetrizedVelocityCurrent SchwartzSpinorOneParticle1D
        (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ)
        (schwartzSpinOperatorLinear ℏ spinComponent) =
      (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ).comp
        (schwartzSpinOperatorLinear ℏ spinComponent) := by
  apply _root_.ConservationLaw.symmetrizedProduct_eq_comp_of_commutes
  change
    ⁅SchwartzTwoLevel1D.spatialLift (SchwartzSchrodinger1D.velocityOperator ℏ κ),
      SchwartzTwoLevel1D.internalOperator
        (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)⁆ = 0
  exact SchwartzTwoLevel1D.lie_spatialLift_internalOperator_eq_zero
    (SchwartzSchrodinger1D.velocityOperator ℏ κ)
    (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)

/-- The current density stored in the local representation is exactly `v S(n)`. -/
theorem schwartzSpinCurrentRepresentation1D_currentDensity_eq_velocity_comp_spin
    (ℏ κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) :
    (schwartzSpinCurrentRepresentation1D ℏ κ potential internalH spinComponent).currentDensity =
      (SchwartzTwoLevelSchrodinger1D.velocityOperator ℏ κ).comp
        (schwartzSpinOperatorLinear ℏ spinComponent) := by
  rw [schwartzSpinCurrentRepresentation1D_currentDensity,
    schwartzSpinCurrentDensityLinear1D_apply]
  exact symmetrizedSpinCurrent_eq_velocity_comp_spin ℏ κ spinComponent

/-- The canonical localized spin source/torque is generated only by the internal Hamiltonian
commutator `[H_internal,S(n)]`. -/
theorem schwartzSpin_sourceCommutator_eq_internal
    (κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix)
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) (f : SchwartzTwoLevel1D.Spatial) :
    _root_.ConservationLaw.sourceCommutator SchwartzSpinorOneParticle1D
        (SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperatorLinear ℏ spinComponent) f =
      _root_.ConservationLaw.symmetrizedProduct
        (SchwartzTwoLevel1D.multiplicationOperator f)
        ⁅SchwartzTwoLevel1D.internalOperator internalH,
          schwartzSpinOperatorLinear ℏ spinComponent⁆ := by
  rw [_root_.ConservationLaw.sourceCommutator]
  change
    _root_.ConservationLaw.symmetrizedProduct
        (SchwartzTwoLevel1D.multiplicationOperator f)
        ⁅SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH,
          SchwartzTwoLevel1D.internalOperator
            (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)⁆ =
      _root_.ConservationLaw.symmetrizedProduct
        (SchwartzTwoLevel1D.multiplicationOperator f)
        ⁅SchwartzTwoLevel1D.internalOperator internalH,
          SchwartzTwoLevel1D.internalOperator
            (QuantumTheory.SpinHalf.spinMatrix ℏ spinComponent)⁆
  rw [SchwartzTwoLevelSchrodinger1D.lie_hamiltonian_internalOperator_eq_internal]

/-- If the internal Hamiltonian conserves the selected spin component, the local spin source
vanishes and the balance law reduces to pure transport. -/
theorem schwartzSpin_sourceCommutator_eq_zero_of_internal_commutes
    (κ : ℝ) (potential : SchwartzTwoLevel1D.Spatial)
    (internalH : SchwartzTwoLevel1D.InternalMatrix)
    (ℏ : ℝ) (spinComponent : QuantumTheory.SpinHalf.SpinSpace) (f : SchwartzTwoLevel1D.Spatial)
    (hcomm : ⁅SchwartzTwoLevel1D.internalOperator internalH,
      schwartzSpinOperatorLinear ℏ spinComponent⁆ = 0) :
    _root_.ConservationLaw.sourceCommutator SchwartzSpinorOneParticle1D
        (SchwartzTwoLevelSchrodinger1D.hamiltonian κ potential internalH)
        SchwartzTwoLevel1D.multiplicationLinear
        (schwartzSpinOperatorLinear ℏ spinComponent) f = 0 := by
  rw [schwartzSpin_sourceCommutator_eq_internal]
  simp [hcomm]

end
end Continuum
end SingleParticle
end QuantumMechanics
