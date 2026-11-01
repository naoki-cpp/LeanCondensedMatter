import LeanCondensedMatter.Transport.KuboBastin.Eigenbasis
import LeanCondensedMatter.Transport.KuboBastin.Finite
import LeanCondensedMatter.Transport.KuboBastin.OccupationInterpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Occupation-resolved finite Kubo–Bastin response

This module owns the statistics-independent bridge from discrete eigenbasis occupation differences
to oriented energy integrals of a supplied occupation derivative. It is generic in the Hilbert
space carrier and in the measured/source response vertices at the transition level, while complete
responses use the finite spectral-index layer from `KuboBastin.Finite`.

```text
finite spectral Kubo–Bastin response
  -> replace pₘ - pₙ by ∫_[Eₙ,Eₘ] f'(E) dE
  -> occupation-resolved vertex / ResponseChannel response.
```

`EigenbasisOccupationInterpolation` supplies the continuous occupation and the fundamental-theorem
boundary. Fermionic lattice currents, Peierls contacts, conductivity normalization, and directional
charge-current specializations remain downstream.

This is not yet a common full-energy Bastin kernel or a Středa surface/sea representation. No
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
variable (data : EnergyEigenbasisLehmannData system ι)

/-- One generalized eigenbasis Kubo–Bastin transition with its discrete occupation difference
replaced by an oriented energy integral of the occupation derivative. -/
noncomputable def eigenbasisKuboBastinOccupationResolvedVertexTerm
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) : ℂ :=
  -(∫ energy in data.energy mn.2..data.energy mn.1,
      interpolation.occupationDerivative energy) *
    eigenbasisKuboBastinVertexTransitionFactor
      system data measured source omega eta mn

/-- The generalized eigenbasis spectral Bastin transition is exactly its occupation-resolved form. -/
theorem eigenbasisKuboBastinSpectralVertexTerm_eq_occupationResolved
    (interpolation : EigenbasisOccupationInterpolation system data)
    (measured source : H →L[ℂ] H)
    (omega eta : ℝ) (mn : ι × ι) :
    eigenbasisKuboBastinSpectralVertexTerm
        system data measured source omega eta mn =
      eigenbasisKuboBastinOccupationResolvedVertexTerm
        system data interpolation measured source omega eta mn := by
  unfold eigenbasisKuboBastinSpectralVertexTerm
    eigenbasisKuboBastinOccupationResolvedVertexTerm
  rw [show (((data.probability mn.1 - data.probability mn.2 : ℝ) : ℂ)) =
      ∫ energy in data.energy mn.2..data.energy mn.1,
        interpolation.occupationDerivative energy by
    simpa using interpolation.probability_sub_eq_integral system mn.1 mn.2]

variable [Fintype ι]

/-- Occupation-resolved generalized response attached directly to a neutral response channel. -/
noncomputable def finiteKuboBastinOccupationResolvedChannelResponse
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) : ℂ :=
  (∑ mn : ι × ι,
      eigenbasisKuboBastinOccupationResolvedVertexTerm
        system data interpolation channel.measured channel.source omega eta mn) +
    eigenbasisNormalizedExpectation system data channel.observableVariation

/-- The occupation-resolved channel response reduces to its aggregate transition sum. -/
theorem finiteKuboBastinOccupationResolvedChannelResponse_eq_vertexSum
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta =
      (∑ mn : ι × ι,
        eigenbasisKuboBastinOccupationResolvedVertexTerm
          system data interpolation channel.measured channel.source omega eta mn) +
        eigenbasisNormalizedExpectation system data channel.observableVariation := by
  rfl

/-- The neutral finite spectral channel response equals its occupation-resolved form. -/
theorem finiteKuboBastinSpectralChannelResponse_eq_occupationResolved
    (interpolation : EigenbasisOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteKuboBastinSpectralChannelResponse system data channel omega eta =
      finiteKuboBastinOccupationResolvedChannelResponse
        system data interpolation channel omega eta := by
  rw [finiteKuboBastinSpectralChannelResponse_eq_vertexSum,
    finiteKuboBastinOccupationResolvedChannelResponse_eq_vertexSum]
  congr 1
  apply Finset.sum_congr rfl
  intro mn _
  exact eigenbasisKuboBastinSpectralVertexTerm_eq_occupationResolved
    system data interpolation channel.measured channel.source omega eta mn

end
end Transport
end QuantumTheory
