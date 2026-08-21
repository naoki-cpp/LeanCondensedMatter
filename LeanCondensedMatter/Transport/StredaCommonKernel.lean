import LeanCondensedMatter.Transport.StredaOccupation

set_option linter.style.header false

/-!
# Common energy kernel for finite Kubo–Bastin response

Finite transition intervals are localized on the full energy axis and summed into one integrable
piecewise kernel.  The construction is statistics-independent and generic in the Hilbert-space
carrier, measured/source vertices, and explicit observable-variation term.

The common kernel is generally discontinuous at spectral energies.  It is therefore not itself the
smooth Středa primitive required by `RegularizedStredaRepresentation`, and equality with the
canonical traced Bastin energy integral is not asserted here.  That identification remains a
separate Ward/energy-representation theorem.

Fermionic lattice currents, Peierls contacts, and conductivity normalization remain downstream.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory LinearResponse Set

noncomputable section

/-- A full-line function encoding the oriented interval integral from `a` to `b`. -/
noncomputable def orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b energy : ℝ) : ℂ :=
  (Ioc a b).indicator f energy - (Ioc b a).indicator f energy

theorem integrable_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    Integrable (orientedIntervalIntegrand f a b) := by
  unfold orientedIntervalIntegrand
  exact (hf.1.integrable_indicator measurableSet_Ioc).sub
    (hf.2.integrable_indicator measurableSet_Ioc)

theorem integral_orientedIntervalIntegrand
    (f : ℝ → ℂ) (a b : ℝ) (hf : IntervalIntegrable f volume a b) :
    (∫ energy : ℝ, orientedIntervalIntegrand f a b energy) =
      ∫ energy in a..b, f energy := by
  unfold orientedIntervalIntegrand
  rw [MeasureTheory.integral_sub
    (hf.1.integrable_indicator measurableSet_Ioc)
    (hf.2.integrable_indicator measurableSet_Ioc)]
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc]
  rfl

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Full-line localized integrand associated with one generalized Bastin transition. -/
noncomputable def finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) (energy : ℝ) : ℂ :=
  orientedIntervalIntegrand
    ((-finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn) •
      interpolation.occupationDerivative)
    (data.energy mn.2) (data.energy mn.1) energy

theorem integrable_finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    Integrable (finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn) := by
  apply integrable_orientedIntervalIntegrand
  exact (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul
    (-finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn)

theorem integral_finiteKuboBastinCommonVertexTransitionIntegrand
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    (∫ energy : ℝ, finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn energy) =
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  let factor := finiteKuboBastinVertexTransitionFactor
    system data measured source omega eta mn
  have hint : IntervalIntegrable ((-factor) • interpolation.occupationDerivative)
      volume (data.energy mn.2) (data.energy mn.1) :=
    (interpolation.occupationDerivative_intervalIntegrable mn.1 mn.2).smul (-factor)
  rw [show finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn =
      orientedIntervalIntegrand ((-factor) • interpolation.occupationDerivative)
        (data.energy mn.2) (data.energy mn.1) by rfl]
  rw [integral_orientedIntervalIntegrand _ _ _ hint]
  change (∫ energy in data.energy mn.2..data.energy mn.1,
      (-factor) • interpolation.occupationDerivative energy) = _
  rw [intervalIntegral.integral_smul]
  unfold finiteKuboBastinOccupationResolvedVertexTerm
  simp only [smul_eq_mul]
  ring

variable [Fintype ι]

/-- Finite sum of all generalized localized transition integrands on the full energy axis. -/
noncomputable def finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (energy : ℝ) : ℂ :=
  ∑ mn : ι × ι, finiteKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn energy

theorem integrable_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    Integrable (finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta) := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  apply integrable_finsetSum
  intro mn _
  exact integrable_finiteKuboBastinCommonVertexTransitionIntegrand
    system data interpolation measured source omega eta mn

theorem integral_finiteKuboBastinCommonVertexEnergyKernel
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) :
    (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta energy) =
      ∑ mn : ι × ι, finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold finiteKuboBastinCommonVertexEnergyKernel
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro mn _
    exact integral_finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn
  · intro mn _
    exact integrable_finiteKuboBastinCommonVertexTransitionIntegrand
      system data interpolation measured source omega eta mn

/-- Generalized common-energy response, with the explicit observable-variation expectation kept
outside the energy kernel. -/
noncomputable def finiteKuboBastinCommonEnergyVertexResponse
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  (∫ energy : ℝ, finiteKuboBastinCommonVertexEnergyKernel
      system data interpolation measured source omega eta energy) +
    purePointNormalizedExpectation system data observableVariation

/-- The generalized occupation-resolved response equals its common-energy-kernel form. -/
theorem finiteKuboBastinOccupationResolvedVertexResponse_eq_commonEnergy
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) :
    finiteKuboBastinOccupationResolvedVertexResponse system data interpolation
        measured source observableVariation omega eta =
      finiteKuboBastinCommonEnergyVertexResponse system data interpolation
        measured source observableVariation omega eta := by
  unfold finiteKuboBastinOccupationResolvedVertexResponse
    finiteKuboBastinCommonEnergyVertexResponse
  rw [integral_finiteKuboBastinCommonVertexEnergyKernel]

/-- Generalized common-energy response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinCommonEnergyChannelResponse
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinCommonEnergyVertexResponse system data interpolation
    channel.measured channel.source channel.observableVariation omega eta

/-- The generalized spectral channel response equals its common-energy-kernel representation. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
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
        system data interpolation channel omega eta := by
      simpa [finiteKuboBastinOccupationResolvedChannelResponse,
        finiteKuboBastinCommonEnergyChannelResponse] using
        finiteKuboBastinOccupationResolvedVertexResponse_eq_commonEnergy
          system data interpolation channel.measured channel.source
            channel.observableVariation omega eta

end
end Transport
end QuantumTheory
