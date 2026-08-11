import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StaticKuboBastinResponse
import LeanCondensedMatter.Transport.StredaSpectralEnergyIntegral

set_option linter.style.header false

/-!
# Static Kubo–Bastin to Středa bridge under a visible Peierls Ward identity

The named static finite-dimensional conductivity retains three pieces which the canonical traced
Bastin energy integral does not contain by definition:

* the current-current vector-potential response;
* the explicit Peierls contact expectation; and
* the finite-volume electric-field normalization `1 / (V (-η))`.

At finite positive switching rate, identifying these objects requires a model-specific Ward/f-sum
identity. This module exposes the minimal identity at the current-current level: the ordinary trace
is the volume/electric-field factor times the canonical traced Bastin integral, minus the contact
expectation. The contact term is therefore not silently dropped, and every scalar factor remains
visible.

Under that identity, the normalization cancels exactly and the named static conductivity equals
the canonical traced Bastin integral. The theorem also constructs the concrete
`RegularizedStredaRepresentation` without an additional ad hoc response-equality argument.

No proof of the model-specific Ward identity is claimed here, and no zero-switching,
zero-broadening, disorder, trace-per-volume, or thermodynamic limit is taken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open QuantumTheory.LinearResponse QuantumTheory.Transport
open SecondQuantization.Fermionic.Field

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- The zero-frequency current-current part of the finite-dimensional vector-potential response,
before adding the Peierls contact expectation. -/
noncomputable def finiteDimensionalStaticKuboBastinCurrentCurrentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
    (finiteKuboBastinDirectionalTraceCarrier
      system data geometry direction K q 0 eta)

/-- The static vector-potential response is exactly the current-current trace plus the explicit
Peierls contact expectation. -/
theorem finiteDimensionalStaticKuboBastinVectorPotentialResponse_eq_currentCurrent_add_contact
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteDimensionalStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      finiteDimensionalStaticKuboBastinCurrentCurrentResponse
          system data geometry direction K q eta +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  rfl

/-- Minimal finite-rate Peierls Ward/f-sum identity needed to identify the named static response
with the canonical traced Bastin energy integral.

The current-current trace equals `V (-η)` times the traced Bastin integral at energy broadening
`ℏη`, minus the contact expectation. Proving this field from a concrete Peierls model is the
remaining model-specific sum-rule problem; using the bridge below requires the field explicitly. -/
structure FiniteStaticPeierlsWardIdentity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : Prop where
  currentCurrent_eq_scaledTracedBastin_sub_contact :
    finiteDimensionalStaticKuboBastinCurrentCurrentResponse
        system data geometry direction K q eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
          regularizedTracedBastinEnergyIntegral
            system.hamiltonian.1
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K)
            (kuboBastinEnergyBroadening system.hbar eta)
            lowerEnergy upperEnergy occupation -
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)

/-- The Ward identity converts the complete vector-potential response, including contact, into the
explicit volume/electric-field factor times the traced Bastin integral. -/
theorem FiniteStaticPeierlsWardIdentity.vectorPotentialResponse_eq_scaledTracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardIdentity convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation) :
    finiteDimensionalStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
        regularizedTracedBastinEnergyIntegral
          system.hamiltonian.1
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (kuboBastinEnergyBroadening system.hbar eta)
          lowerEnergy upperEnergy occupation := by
  rw [finiteDimensionalStaticKuboBastinVectorPotentialResponse_eq_currentCurrent_add_contact]
  rw [ward.currentCurrent_eq_scaledTracedBastin_sub_contact]
  ring

/-- At positive switching rate, the visible Ward identity cancels the exact finite-volume
zero-frequency normalization and identifies the named static conductivity with the canonical
traced Bastin energy integral. -/
theorem FiniteStaticPeierlsWardIdentity.staticConductivity_eq_tracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardIdentity convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  rw [finiteDimensionalStaticKuboBastinDirectionalConductivity_eq_vectorPotential]
  rw [ward.vectorPotentialResponse_eq_scaledTracedBastin]
  rw [finiteVolumeConductivityNormalization_zero_frequency]
  let denominator : ℂ := (convention.volume : ℂ) * (-(eta : ℂ))
  let integral : ℂ := regularizedTracedBastinEnergyIntegral
    system.hamiltonian.1
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (kuboBastinEnergyBroadening system.hbar eta)
    lowerEnergy upperEnergy occupation
  have hdenominator : denominator ≠ 0 := by
    dsimp [denominator]
    simpa using finiteVolumeConductivityDenominator_ne_zero convention 0 eta heta
  change (denominator * integral) * denominator⁻¹ = integral
  calc
    (denominator * integral) * denominator⁻¹ =
        integral * (denominator * denominator⁻¹) := by ring
    _ = integral := by simp [hdenominator]

/-- The same bridge written directly in the finite pure-point spectral energy-integral form. -/
theorem FiniteStaticPeierlsWardIdentity.staticConductivity_eq_spectralEnergyIntegral
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardIdentity convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      regularizedBastinSpectralEnergyIntegral
        system data
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  calc
    _ = regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation :=
      ward.staticConductivity_eq_tracedBastin
        convention system data geometry direction K q eta
          lowerEnergy upperEnergy occupation heta
    _ = _ := regularizedTracedBastinEnergyIntegral_eq_spectral
      system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation
      (kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta)

/-- The analytic traced-kernel data and the visible Ward identity construct the concrete Středa
representation of the named static finite-dimensional conductivity. -/
noncomputable def TracedStredaAnalyticData.toStaticKuboBastinStredaRepresentation
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (spectralData : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    (analyticData : TracedStredaAnalyticData
      system.hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (ward : FiniteStaticPeierlsWardIdentity convention system spectralData
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    RegularizedStredaRepresentation
      (finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system spectralData geometry direction K q eta) :=
  analyticData.toRegularizedStredaRepresentation
    (finiteDimensionalStaticKuboBastinDirectionalConductivity
      convention system spectralData geometry direction K q eta)
    (ward.staticConductivity_eq_tracedBastin
      convention system spectralData geometry direction K q eta
        lowerEnergy upperEnergy occupation heta)

/-- The resulting named static conductivity has the regularized Středa surface-plus-sea split. -/
theorem TracedStredaAnalyticData.staticKuboBastinConductivity_eq_surface_add_sea
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (spectralData : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    (analyticData : TracedStredaAnalyticData
      system.hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (ward : FiniteStaticPeierlsWardIdentity convention system spectralData
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system spectralData geometry direction K q eta =
      regularizedStredaFermiSurface analyticData.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea analyticData.toRegularizedStredaIntegralData :=
  (analyticData.toStaticKuboBastinStredaRepresentation
    convention system spectralData geometry direction K q eta
      lowerEnergy upperEnergy occupation occupationDerivative ward heta).response_eq_surface_add_sea

end
end Transport
end Fermionic
end SecondQuantization
