import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.Streda.ResponseMatrixRepresentation

set_option linter.style.header false

/-!
# Massive-Dirac Středa fiber response

This module packages the two in-plane charge-current directions of one clean massive-Dirac momentum
fiber into shared-provenance Středa response data. Every component therefore uses the same
Hamiltonian, finite broadening, energy interval, occupation, and occupation derivative.

These fixed-momentum quantities are response contributions, not yet physical conductivities. The
Bastin prefactor, angular integration, and physical momentum measure must be supplied downstream
before constructing a conductivity tensor. The full ordered fiber response is retained here rather
than selecting longitudinal or Hall projections before that physical normalization.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Shared analytic Středa data for all `x/y` current pairs of one massive-Dirac momentum fiber. -/
abbrev MassiveDiracStredaFiberAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaResponseMatrixAnalyticData
    (hamiltonianOperator v m px py)
    (fun direction => currentOperator direction e v)
    broadening lowerEnergy upperEnergy occupation occupationDerivative

/-- Complete finite-broadening Středa response of one momentum fiber for one ordered current pair.
This is not yet a conductivity because continuum momentum normalization has not been applied. -/
noncomputable def massiveDiracStredaFiberTotalResponse
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (measured source : Direction2) : ℂ :=
  data.toStaticStredaResponseMatrix.total measured source

/-- Every ordered fiber response is exactly the traced Bastin energy integral for the corresponding
pair of physical charge-current directions under the same analytic setup. -/
theorem massiveDiracStredaFiberTotalResponse_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (measured source : Direction2) :
    massiveDiracStredaFiberTotalResponse data measured source =
      regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator measured e v) (currentOperator source e v)
        broadening lowerEnergy upperEnergy occupation := by
  unfold massiveDiracStredaFiberTotalResponse
  exact data.toStaticStredaResponseMatrix_total_eq_tracedBastin measured source

end

end AnomalousHall.MassiveDirac
