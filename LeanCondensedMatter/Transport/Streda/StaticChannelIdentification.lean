import LeanCondensedMatter.Transport.Streda.GeneralizedStatic
import LeanCondensedMatter.Transport.Streda.SpectralEnergyIntegral
import LeanCondensedMatter.Transport.Core.ConductivityNormalization

set_option linter.style.header false

/-!
# Conditional identification of a complete static channel response with a traced Bastin integral

The required equality relates the vertex response to `V (-η)` times the traced integral,
minus the observable-variation expectation. It is an explicit assumption, not a proved Ward
identity of any model. Measured and source vertices are independent.

After adding the observable variation, the finite-volume electric-field normalization cancels.
This concerns the complete response; the vertex-only Středa representation in `GeneralizedStatic`
has a different input. No zero-rate, DC, disorder, or thermodynamic limit is taken here.
-/

namespace QuantumTheory.Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [FiniteDimensional ℂ H]

/-- The supplied identity needed to cancel the observable variation and static normalization.
In a Peierls model its proof is a model-specific Ward/f-sum problem. -/
structure StaticChannelTracedBastinIdentity
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ) : Prop where
  vertexResponse_eq_scaledTracedBastin_sub_observableVariation :
    finiteStaticKuboBastinChannelVertexResponse system data channel eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
        regularizedTracedBastinEnergyIntegral system.hamiltonian.1
        channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation -
      eigenbasisNormalizedExpectation system data channel.observableVariation

/-- The assumed identity identifies the complete response, including observable variation. -/
theorem StaticChannelTracedBastinIdentity.channelResponse_eq_scaledTracedBastin
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (identity : StaticChannelTracedBastinIdentity convention system data channel
      eta lowerEnergy upperEnergy occupation) :
    finiteStaticKuboBastinChannelResponse system data channel eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
        regularizedTracedBastinEnergyIntegral system.hamiltonian.1
        channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  change finiteKuboBastinSpectralChannelResponse system data channel 0 eta = _
  rw [finiteKuboBastinSpectralChannelResponse_eq_vertexSum]
  change finiteStaticKuboBastinChannelVertexResponse system data channel eta +
    eigenbasisNormalizedExpectation system data channel.observableVariation = _
  rw [identity.vertexResponse_eq_scaledTracedBastin_sub_observableVariation]
  ring

/-- Nonzero switching rate permits cancellation of the exact static normalization. -/
theorem StaticChannelTracedBastinIdentity.staticConductivity_eq_tracedBastin
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (identity : StaticChannelTracedBastinIdentity convention system data channel
      eta lowerEnergy upperEnergy occupation) (heta : eta ≠ 0) :
    finiteVolumeConductivityFromVectorPotential convention 0 eta
      (finiteStaticKuboBastinChannelResponse system data channel eta) =
      regularizedTracedBastinEnergyIntegral system.hamiltonian.1
        channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  unfold finiteVolumeConductivityFromVectorPotential
  rw [identity.channelResponse_eq_scaledTracedBastin]
  rw [finiteVolumeConductivityNormalization_zero_frequency]
  let denominator : ℂ := (convention.volume : ℂ) * (-(eta : ℂ))
  let integral : ℂ := regularizedTracedBastinEnergyIntegral system.hamiltonian.1
    channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
    lowerEnergy upperEnergy occupation
  have hdenominator : denominator ≠ 0 := by
    dsimp [denominator]
    simpa [adiabaticElectricFieldFactor] using
      finiteVolumeConductivityDenominator_ne_zero convention 0 eta (Or.inr heta)
  change (denominator * integral) * denominator⁻¹ = integral
  calc
    (denominator * integral) * denominator⁻¹ =
        integral * (denominator * denominator⁻¹) := by ring
    _ = integral := by simp [hdenominator]

/-- At positive switching rate the same conditional identification has a spectral form. -/
theorem StaticChannelTracedBastinIdentity.staticConductivity_eq_spectralEnergyIntegral
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (identity : StaticChannelTracedBastinIdentity convention system data channel
      eta lowerEnergy upperEnergy occupation) (heta : 0 < eta) :
    finiteVolumeConductivityFromVectorPotential convention 0 eta
      (finiteStaticKuboBastinChannelResponse system data channel eta) =
      regularizedBastinSpectralEnergyIntegral system data channel.measured channel.source
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  rw [identity.staticConductivity_eq_tracedBastin convention system data channel
    eta lowerEnergy upperEnergy occupation heta.ne']
  exact regularizedTracedBastinEnergyIntegral_eq_spectral system data
    channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
    lowerEnergy upperEnergy occupation
    (kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta)

/-- Analytic traced-kernel data and the explicit identity give the normalized complete response
a Středa representation. -/
noncomputable def TracedStredaAnalyticData.toStaticChannelStredaRepresentation
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (occupationDerivative : ℝ → ℂ)
    (analyticData : TracedStredaAnalyticData system.hamiltonian.1
      channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (identity : StaticChannelTracedBastinIdentity convention system data channel
      eta lowerEnergy upperEnergy occupation) (heta : eta ≠ 0) :
    RegularizedStredaRepresentation
      (finiteVolumeConductivityFromVectorPotential convention 0 eta
        (finiteStaticKuboBastinChannelResponse system data channel eta)) :=
  analyticData.toRegularizedStredaRepresentation _
    (identity.staticConductivity_eq_tracedBastin convention system data channel
      eta lowerEnergy upperEnergy occupation heta)

/-- The identified normalized complete response has the regularized surface-plus-sea split. -/
theorem TracedStredaAnalyticData.staticChannelConductivity_eq_surface_add_sea
    (convention : PositiveVolume)
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (channel : ResponseChannel H)
    (eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (occupationDerivative : ℝ → ℂ)
    (analyticData : TracedStredaAnalyticData system.hamiltonian.1
      channel.measured channel.source (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (identity : StaticChannelTracedBastinIdentity convention system data channel
      eta lowerEnergy upperEnergy occupation) (heta : eta ≠ 0) :
    finiteVolumeConductivityFromVectorPotential convention 0 eta
      (finiteStaticKuboBastinChannelResponse system data channel eta) =
      regularizedStredaFermiSurface analyticData.toRegularizedStredaIntegralData +
        regularizedStredaFermiSea analyticData.toRegularizedStredaIntegralData :=
  (analyticData.toStaticChannelStredaRepresentation convention system data channel
    eta lowerEnergy upperEnergy occupation occupationDerivative identity heta).response_eq_surface_add_sea

end
end QuantumTheory.Transport
