import LeanCondensedMatter.Transport.Streda.TraceSpectral
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Finite spectral form of the traced Středa energy integral

The canonical finite-dimensional Bastin energy integral is the occupation-weighted interval
integral of the ordinary-trace resolvent kernel. The preceding pure-point layer expands that kernel
pointwise at every strictly positive broadening.

This module lifts the pointwise theorem through the energy integral and names the resulting finite
spectral energy integral. It does not identify that integral with the finite-switching Kubo
conductivity, cancel the Peierls contact term, apply the electric-field normalization, or take a
zero-broadening or thermodynamic limit.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype ι] [FiniteDimensional ℂ H]

/-- Occupation-weighted finite pure-point spectral energy integral associated with the canonical
ordinary-trace Bastin kernel. -/
noncomputable def regularizedBastinSpectralEnergyIntegral
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : ℂ :=
  ∫ energy in lowerEnergy..upperEnergy,
    occupation energy *
      regularizedBastinSpectralTraceSum
        system data current₁ current₂ energy broadening

/-- At positive broadening, the canonical traced Bastin energy integral is exactly its finite
pure-point spectral energy integral. -/
theorem regularizedTracedBastinEnergyIntegral_eq_spectral
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (current₁ current₂ : H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) (hbroadening : 0 < broadening) :
    regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1 current₁ current₂ broadening
          lowerEnergy upperEnergy occupation =
      regularizedBastinSpectralEnergyIntegral
        system data current₁ current₂ broadening
          lowerEnergy upperEnergy occupation := by
  unfold regularizedTracedBastinEnergyIntegral
    regularizedBastinSpectralEnergyIntegral
  simp_rw [regularizedBastinTraceIntegrand_eq_spectral_sum
    system data current₁ current₂ _ broadening hbroadening]

end
end Transport
end QuantumTheory
