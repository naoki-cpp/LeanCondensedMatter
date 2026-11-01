import LeanCondensedMatter.Analysis.Calculus.IntervalLocalization
import LeanCondensedMatter.Transport.KuboBastin.Eigenbasis
import LeanCondensedMatter.Transport.KuboBastin.Occupation

set_option linter.style.header false

/-!
# Common energy kernel for finite Kubo–Bastin response

Finite transition intervals are localized on the full energy axis and summed into one integrable
piecewise kernel. The representation-independent full-line interval localization is owned upstream
by `Analysis.Calculus.IntervalLocalization`; this module owns its Kubo–Bastin specialization. The
transition-level construction is eigenbasis and does not require a finite spectral index; finite
sums first enter at the common-energy kernel.

The common kernel is generally discontinuous at spectral energies. It is therefore not itself the
smooth Středa primitive required by `RegularizedStredaRepresentation`, and equality with the
canonical traced Bastin energy integral is not asserted here. That identification remains a
separate Ward/energy-representation theorem.

Fermionic lattice currents, Peierls contacts, and conductivity normalization remain downstream.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory LinearResponse Set

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Full-line localized integrand associated with one generalized eigenbasis Bastin transition. -/
noncomputable def eigenbasisKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) (energy : ℝ) : ℂ :=
  orientedIntervalIntegrand
    ((-eigenbasisKuboBastinVertexTransitionFactor
      system data measured source omega eta mn) •
      interpolation.occupationDerivative)
    (data.energy mn.2) (data.energy mn.1) energy

theorem integrable_eigenbasisKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    Integrable (eigenbasisKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn) := by
  apply integrable_orientedIntervalIntegrand
  exact (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul
    (-eigenbasisKuboBastinVertexTransitionFactor
      system data measured source omega eta mn)

theorem integral_eigenbasisKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    (∫ energy : ℝ, eigenbasisKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn energy) =
      eigenbasisKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  let factor := eigenbasisKuboBastinVertexTransitionFactor
    system data measured source omega eta mn
  have hint : IntervalIntegrable ((-factor) • interpolation.occupationDerivative)
      volume (data.energy mn.2) (data.energy mn.1) :=
    (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul (-factor)
  rw [show eigenbasisKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn =
      orientedIntervalIntegrand ((-factor) • interpolation.occupationDerivative)
        (data.energy mn.2) (data.energy mn.1) by rfl]
  rw [integral_orientedIntervalIntegrand _ _ _ hint]
  change (∫ energy in data.energy mn.2..data.energy mn.1,
      (-factor) • interpolation.occupationDerivative energy) = _
  rw [intervalIntegral.integral_smul]
  unfold eigenbasisKuboBastinOccupationResolvedVertexTerm
  simp only [smul_eq_mul]
  ring

variable [Fintype ι]

/-- Finite sum of all generalized localized transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, eigenbasisKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn energy

theorem integrable_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta) := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  apply integrable_finsetSum
  intro mn _
  exact integrable_eigenbasisKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn

theorem integral_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta energy) =
      ∑ mn : ι × ι, eigenbasisKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro mn _
    exact integral_eigenbasisKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn
  · intro mn _
    exact integrable_eigenbasisKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn

/-- Generalized common-energy response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinCommonEnergyChannelResponse
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation channel.measured channel.source omega eta energy) +
    eigenbasisNormalizedExpectation system data channel.observableVariation

/-- The generalized occupation-resolved channel response equals its common-energy-kernel
representation. -/
theorem finiteKuboBastinOccupationResolvedChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta =
      finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta := by
  rw [finiteKuboBastinOccupationResolvedChannelResponse_eq_vertexSum]
  unfold finiteKuboBastinCommonEnergyChannelResponse
  rw [integral_finiteKuboBastinCommonVertexEnergyKernel]

theorem finiteKuboBastinSpectralChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem H)
    (data : EnergyEigenbasisLehmannData system ι)
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta := by
  calc
    _ = finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta :=
      finiteKuboBastinSpectralChannelResponse_eq_occupationResolved
        system data interpolation channel omega eta
    _ = finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta :=
      finiteKuboBastinOccupationResolvedChannelResponse_eq_commonEnergy
        system data interpolation channel omega eta

end
end Transport
end QuantumTheory
