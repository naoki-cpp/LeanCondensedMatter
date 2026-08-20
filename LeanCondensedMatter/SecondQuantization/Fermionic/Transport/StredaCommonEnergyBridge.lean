import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StredaCommonKernel

set_option linter.style.header false

/-!
# Ordinary finite-dimensional Kubo–Bastin to common-energy bridge

This file closes the API boundary between the ordinary finite-dimensional `ResponseChannel`
representation used by the generalized static/Středa layer and the occupation-resolved common-energy
representation.  It does not identify the common-energy kernel with a canonical smooth Středa
integral; that remains a separate Ward/energy-representation problem.
-/

namespace SecondQuantization.Fermionic.Transport

open SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site ι : Type*}
variable [Fintype Site] [Fintype ι]

/-- The ordinary finite-dimensional generalized Kubo–Bastin channel response is exactly the
occupation-interpolated common-energy response.

The first equality is the existing ordinary-trace/spectral bridge; the second is the generalized
occupation/common-energy bridge.  The explicit observable-variation/contact expectation is
therefore preserved unchanged across the complete chain. -/
theorem finiteDimensionalKuboBastinChannelResponse_eq_commonEnergy
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (interpolation : PurePointOccupationInterpolation system data)
    (channel : ResponseChannel (FiniteLatticeHilbertFock Site))
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
end SecondQuantization.Fermionic.Transport
