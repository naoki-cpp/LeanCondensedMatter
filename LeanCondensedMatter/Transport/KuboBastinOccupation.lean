import LeanCondensedMatter.Transport.FiniteKuboBastin
import LeanCondensedMatter.Transport.OccupationInterpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Occupation-resolved finite Kubo–Bastin response

This module owns the statistics-independent bridge from discrete pure-point occupation differences
to oriented energy integrals of a supplied occupation derivative.  It is generic in the Hilbert
space carrier and in the measured/source response vertices.

```text
finite spectral Kubo–Bastin response
  -> replace pₘ - pₙ by ∫_[Eₙ,Eₘ] f'(E) dE
  -> occupation-resolved vertex / ResponseChannel response.
```

`PurePointOccupationInterpolation` supplies the continuous occupation and the fundamental-theorem
boundary.  Fermionic lattice currents, Peierls contacts, conductivity normalization, and directional
charge-current specializations remain downstream.

This is not yet a common full-energy Bastin kernel or a Středa surface/sea representation.  No
zero-temperature distributional derivative, zero-broadening, DC, disorder, trace-per-volume, or
thermodynamic-limit statement is made here.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)
variable (data : PurePointLehmannData system ι)

/-- Matrix elements and retarded-resolvent factor of one finite generalized Bastin transition,
with the occupation difference removed. -/
noncomputable def finiteKuboBastinVertexTransitionFactor
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  inner ℂ (data.basis mn.1) (measured (data.basis mn.2)) *
    inner ℂ (data.basis mn.2) (source (data.basis mn.1)) *
    inner ℂ (data.basis mn.2)
      (retardedResolvent system.hamiltonian.1
        (kuboBastinRetardedEnergy system.hbar omega (data.energy mn.1))
        (kuboBastinEnergyBroadening system.hbar eta)
        (data.basis mn.2))

/-- One generalized Kubo–Bastin transition with its discrete occupation difference replaced by an
oriented energy integral of the occupation derivative. -/
noncomputable def finiteKuboBastinOccupationResolvedVertexTerm
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  -(∫ energy in data.energy mn.2..data.energy mn.1,
      interpolation.occupationDerivative energy) *
    finiteKuboBastinVertexTransitionFactor
      system data measured source omega eta mn

/-- The generalized spectral Bastin transition is exactly its occupation-resolved form. -/
theorem finiteKuboBastinSpectralVertexTerm_eq_occupationResolved
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    finiteKuboBastinSpectralVertexTerm
        system data measured source omega eta mn =
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold finiteKuboBastinSpectralVertexTerm
    finiteKuboBastinOccupationResolvedVertexTerm
    finiteKuboBastinVertexTransitionFactor
  rw [interpolation.probabilityDifference_eq_integral system mn.1 mn.2]
  ring

variable [Fintype ι]

/-- Complete generalized response after replacing every discrete probability difference by its
oriented occupation-derivative integral. The explicit observable-variation expectation is kept
unchanged. -/
noncomputable def finiteKuboBastinOccupationResolvedVertexResponse
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) : ℂ :=
  (∑ mn : ι × ι,
      finiteKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn) +
    purePointNormalizedExpectation system data observableVariation

/-- The generalized finite spectral Bastin response equals its occupation-resolved form. -/
theorem finiteKuboBastinSpectralVertexResponse_eq_occupationResolved
    (interpolation : PurePointOccupationInterpolation system data)
    (measured source observableVariation : H →L[ℂ] H)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralVertexResponse
        system data measured source observableVariation omega eta =
      finiteKuboBastinOccupationResolvedVertexResponse
        system data interpolation measured source observableVariation omega eta := by
  unfold finiteKuboBastinSpectralVertexResponse
    finiteKuboBastinOccupationResolvedVertexResponse
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact finiteKuboBastinSpectralVertexTerm_eq_occupationResolved
    system data interpolation measured source omega eta mn

/-- Occupation-resolved generalized response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinOccupationResolvedChannelResponse
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  finiteKuboBastinOccupationResolvedVertexResponse system data interpolation
    channel.measured channel.source channel.observableVariation omega eta

/-- The neutral finite spectral channel response equals its occupation-resolved form. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_occupationResolved
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta := by
  simpa [finiteKuboBastinSpectralChannelResponse,
    finiteKuboBastinOccupationResolvedChannelResponse] using
    finiteKuboBastinSpectralVertexResponse_eq_occupationResolved
      system data interpolation channel.measured channel.source
        channel.observableVariation omega eta

end
end Transport
end QuantumTheory
