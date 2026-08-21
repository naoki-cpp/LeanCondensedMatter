import LeanCondensedMatter.Transport.StredaCommonKernel

set_option linter.style.header false

/-!
# Ordinary finite-dimensional Kubo–Bastin to common-energy bridge

This module closes the statistics-independent API boundary between the ordinary finite-dimensional
`ResponseChannel` representation and the occupation-resolved common-energy representation.

It does not identify the common-energy kernel with a canonical smooth Středa integral; that remains
a separate Ward/energy-representation problem. Fermionic lattice currents and model-specific
conductivity specializations remain downstream.
-/

namespace QuantumTheory
namespace Transport

open LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype ι]

/-- The ordinary finite-dimensional generalized Kubo–Bastin channel response is exactly the
occupation-interpolated common-energy response.

The first equality is the ordinary-trace/spectral bridge; the second is the
occupation/common-energy bridge. The explicit observable-variation expectation is therefore
preserved unchanged across the complete chain. -/
theorem finiteDimensionalKuboBastinChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel H)
    (omega eta : ℝ) :
    finiteDimensionalKuboBastinChannelResponse system data channel omega eta =
      finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta := by
  calc
    _ = finiteKuboBastinSpectralChannelResponse system data channel omega eta := by
      simpa [finiteDimensionalKuboBastinChannelResponse,
        finiteKuboBastinSpectralChannelResponse] using
        finiteDimensionalKuboBastinVertexResponse_eq_spectral
          system data channel.measured channel.source channel.observableVariation omega eta
    _ = finiteKuboBastinCommonEnergyChannelResponse
        system data interpolation channel omega eta :=
      finiteKuboBastinSpectralChannelResponse_eq_commonEnergy
        system data interpolation channel omega eta

end
end Transport
end QuantumTheory
