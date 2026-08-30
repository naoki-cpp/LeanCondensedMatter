import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StaticKuboBastinResponse
import LeanCondensedMatter.Transport.Streda.SpectralEnergyIntegral

set_option linter.style.header false

/-!
# Static Kubo–Bastin to Středa bridge under a visible Peierls Ward identity

The finite static Kubo response keeps measured-current and source-field coordinates independent. Its
vertex response, explicit Peierls contact, and electric-field normalization are not by themselves a
Středa representation. At finite positive switching rate, identifying a conductivity component with
the canonical traced Bastin energy integral requires a model-specific Ward/f-sum identity.

This module exposes that identity first for a general component `ij`. Under it, the Peierls contact
cancels against the corresponding term in the Ward relation and the normalization cancels the
explicit `V (-η)` factor. The resulting normalized conductivity component is then equipped with a
`RegularizedStredaRepresentation`, so a complete coordinate family can be assembled into the static
Středa conductivity matrix.

The historical one-direction Ward API is retained below as the diagonal specialization used by
existing finite-disorder consumers. No proof of a model-specific Ward identity is claimed here, and
no zero-switching, zero-broadening, disorder, trace-per-volume, or thermodynamic limit is taken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Componentwise finite-rate Peierls Ward/f-sum identity. The two-vertex response for current
measured along `measuredDirection` and source applied along `sourceDirection` equals `V (-η)` times
the canonical traced Bastin integral, minus the mixed Peierls contact response. -/
structure FiniteStaticPeierlsWardComponentIdentity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : Prop where
  vertex_eq_scaledTracedBastin_sub_contact :
    finiteStaticKuboBastinVectorPotentialVertexComponentResponse
        system data geometry measuredDirection sourceDirection K q eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
          regularizedTracedBastinEnergyIntegral
            system.hamiltonian.1
            (boundedDirectionalCurrent geometry measuredDirection
              (system.hbar : ℂ) (q : ℂ) K)
            (boundedDirectionalCurrent geometry sourceDirection
              (system.hbar : ℂ) (q : ℂ) K)
            (kuboBastinEnergyBroadening system.hbar eta)
            lowerEnergy upperEnergy occupation -
        finiteStaticPeierlsContactComponentResponse
          system data geometry measuredDirection sourceDirection K q

/-- The component Ward identity converts the full vector-potential response, including the mixed
contact term, into the explicit `V (-η)` factor times the traced Bastin integral. -/
theorem FiniteStaticPeierlsWardComponentIdentity.vectorPotentialResponse_eq_scaledTracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardComponentIdentity convention system data geometry
      measuredDirection sourceDirection K q eta lowerEnergy upperEnergy occupation) :
    finiteStaticKuboBastinVectorPotentialComponentResponse
        system data geometry measuredDirection sourceDirection K q eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
        regularizedTracedBastinEnergyIntegral
          system.hamiltonian.1
          (boundedDirectionalCurrent geometry measuredDirection
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry sourceDirection
            (system.hbar : ℂ) (q : ℂ) K)
          (kuboBastinEnergyBroadening system.hbar eta)
          lowerEnergy upperEnergy occupation := by
  rw [finiteStaticKuboBastinVectorPotentialComponentResponse_eq_vertex_add_contact]
  rw [ward.vertex_eq_scaledTracedBastin_sub_contact]
  ring

/-- At positive switching rate, the component Ward identity cancels the exact finite-volume
zero-frequency normalization and identifies `σ_ij` with the canonical traced Bastin integral. -/
theorem FiniteStaticPeierlsWardComponentIdentity.staticConductivityComponent_eq_tracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardComponentIdentity convention system data geometry
      measuredDirection sourceDirection K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteStaticKuboBastinConductivityComponent
        convention system data geometry measuredDirection sourceDirection K q eta =
      regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry measuredDirection
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry sourceDirection
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  unfold finiteStaticKuboBastinConductivityComponent
  rw [ward.vectorPotentialResponse_eq_scaledTracedBastin]
  rw [finiteVolumeConductivityNormalization_zero_frequency]
  let denominator : ℂ := (convention.volume : ℂ) * (-(eta : ℂ))
  let integral : ℂ := regularizedTracedBastinEnergyIntegral
    system.hamiltonian.1
    (boundedDirectionalCurrent geometry measuredDirection
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry sourceDirection
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

/-- Traced Středa analytic data plus a component Ward identity construct the Středa representation
of the normalized physical conductivity component. -/
noncomputable def TracedStredaAnalyticData.toStaticKuboBastinComponentStredaRepresentation
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (spectralData : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    (analyticData : TracedStredaAnalyticData
      system.hamiltonian.1
      (boundedDirectionalCurrent geometry measuredDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry sourceDirection
        (system.hbar : ℂ) (q : ℂ) K)
      (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (ward : FiniteStaticPeierlsWardComponentIdentity convention system spectralData geometry
      measuredDirection sourceDirection K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    RegularizedStredaRepresentation
      (finiteStaticKuboBastinConductivityComponent
        convention system spectralData geometry measuredDirection sourceDirection K q eta) :=
  analyticData.toRegularizedStredaRepresentation
    (finiteStaticKuboBastinConductivityComponent
      convention system spectralData geometry measuredDirection sourceDirection K q eta)
    (ward.staticConductivityComponent_eq_tracedBastin
      convention system spectralData geometry measuredDirection sourceDirection K q eta
        lowerEnergy upperEnergy occupation heta)

/-- The zero-frequency current-current part of the historical diagonal finite spectral
vector-potential response, before adding the Peierls contact expectation. -/
noncomputable def finiteStaticKuboBastinCurrentCurrentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralVertexSum system data
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    0 eta

/-- The historical diagonal static vector-potential response is exactly the current-current spectral
sum plus the explicit Peierls contact expectation. -/
theorem finiteStaticKuboBastinVectorPotentialResponse_eq_currentCurrent_add_contact
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      finiteStaticKuboBastinCurrentCurrentResponse
          system data geometry direction K q eta +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  rw [finiteStaticKuboBastinVectorPotentialResponse_eq_finite_sum]
  unfold finiteStaticKuboBastinCurrentCurrentResponse
    finiteKuboBastinSpectralVertexSum
    finiteKuboBastinSpectralDirectionalCurrentTerm
  rfl

/-- Historical diagonal finite-rate Peierls Ward/f-sum identity. -/
structure FiniteStaticPeierlsWardIdentity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : Prop where
  currentCurrent_eq_scaledTracedBastin_sub_contact :
    finiteStaticKuboBastinCurrentCurrentResponse
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

/-- The diagonal Ward identity converts the complete vector-potential response, including contact,
into the explicit volume/electric-field factor times the traced Bastin integral. -/
theorem FiniteStaticPeierlsWardIdentity.vectorPotentialResponse_eq_scaledTracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (ward : FiniteStaticPeierlsWardIdentity convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation) :
    finiteStaticKuboBastinVectorPotentialResponse
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
  rw [finiteStaticKuboBastinVectorPotentialResponse_eq_currentCurrent_add_contact]
  rw [ward.currentCurrent_eq_scaledTracedBastin_sub_contact]
  ring

/-- At positive switching rate, the diagonal Ward identity identifies the named static conductivity
with the canonical traced Bastin energy integral. -/
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
    finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  rw [finiteStaticKuboBastinDirectionalConductivity_eq_vectorPotential]
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

/-- The same diagonal bridge written directly in the finite pure-point spectral energy-integral
form. -/
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
    finiteStaticKuboBastinDirectionalConductivity
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

/-- The analytic traced-kernel data and the historical diagonal Ward identity construct the concrete
Středa representation of the named static finite spectral conductivity. -/
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
      (finiteStaticKuboBastinDirectionalConductivity
        convention system spectralData geometry direction K q eta) :=
  analyticData.toRegularizedStredaRepresentation
    (finiteStaticKuboBastinDirectionalConductivity
      convention system spectralData geometry direction K q eta)
    (ward.staticConductivity_eq_tracedBastin
      convention system spectralData geometry direction K q eta
        lowerEnergy upperEnergy occupation heta)

/-- The resulting diagonal named static conductivity has the regularized Středa surface-plus-sea
split. -/
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
    finiteStaticKuboBastinDirectionalConductivity
        convention system spectralData geometry direction K q eta =
      regularizedStredaFermiSurface analyticData.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea analyticData.toRegularizedStredaIntegralData :=
  (SecondQuantization.Fermionic.Transport.TracedStredaAnalyticData.toStaticKuboBastinStredaRepresentation
    convention system spectralData geometry direction K q eta
      lowerEnergy upperEnergy occupation occupationDerivative analyticData ward heta).response_eq_surface_add_sea

end
end Transport
end Fermionic
end SecondQuantization
