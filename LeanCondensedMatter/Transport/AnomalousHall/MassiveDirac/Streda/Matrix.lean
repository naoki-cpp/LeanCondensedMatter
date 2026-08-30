import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.Streda.MatrixRepresentation

set_option linter.style.header false

/-!
# Massive-Dirac Středa fiber-response matrix

This module packages the two in-plane charge-current directions of one clean massive-Dirac momentum
fiber into shared-provenance Středa response data. Every component therefore uses the same
Hamiltonian, finite broadening, energy interval, occupation, and occupation derivative.

These fixed-momentum quantities are response contributions, not yet physical conductivities. The
Bastin prefactor, angular integration, and physical momentum measure must be supplied downstream
before constructing a conductivity matrix. Longitudinal and Hall projections are nevertheless
formed here from the same shared fiber response.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Shared analytic Středa data for all `x/y` current pairs of one massive-Dirac momentum fiber. -/
abbrev MassiveDiracStredaFiberAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaMatrixAnalyticData
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
  data.fermiSurfaceMatrix measured source + data.fermiSeaMatrix measured source

/-- Diagonal response contribution of one momentum fiber. -/
noncomputable def massiveDiracStredaFiberLongitudinalResponse
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (direction : Direction2) : ℂ :=
  massiveDiracStredaFiberTotalResponse data direction direction

/-- Antisymmetric in-plane Hall response contribution of one momentum fiber. -/
noncomputable def massiveDiracStredaFiberHallResponse
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) : ℂ :=
  (massiveDiracStredaFiberTotalResponse data .x .y -
    massiveDiracStredaFiberTotalResponse data .y .x) / 2

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
  simpa [massiveDiracStredaFiberTotalResponse,
    TracedStredaMatrixAnalyticData.toStaticStredaConductivityMatrix,
    StaticStredaConductivityMatrix.total] using
    data.toStaticStredaConductivityMatrix_total_eq_tracedBastin measured source

/-- The diagonal fiber response is the corresponding diagonal traced Bastin energy integral. -/
theorem massiveDiracStredaFiberLongitudinalResponse_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (direction : Direction2) :
    massiveDiracStredaFiberLongitudinalResponse data direction =
      regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator direction e v) (currentOperator direction e v)
        broadening lowerEnergy upperEnergy occupation := by
  unfold massiveDiracStredaFiberLongitudinalResponse
  exact massiveDiracStredaFiberTotalResponse_eq_tracedBastin data direction direction

/-- The in-plane Hall fiber response is the antisymmetric `x-y` projection of the same shared
Středa data. -/
theorem massiveDiracStredaFiberHallResponse_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    massiveDiracStredaFiberHallResponse data =
      (regularizedTracedBastinEnergyIntegral
          (hamiltonianOperator v m px py)
          (currentOperator .x e v) (currentOperator .y e v)
          broadening lowerEnergy upperEnergy occupation -
        regularizedTracedBastinEnergyIntegral
          (hamiltonianOperator v m px py)
          (currentOperator .y e v) (currentOperator .x e v)
          broadening lowerEnergy upperEnergy occupation) / 2 := by
  unfold massiveDiracStredaFiberHallResponse
  rw [massiveDiracStredaFiberTotalResponse_eq_tracedBastin data .x .y,
    massiveDiracStredaFiberTotalResponse_eq_tracedBastin data .y .x]

/-- The historical `x-y` scalar Bastin response is the `x-y` entry of the shared fiber response. -/
theorem massiveDiracStredaFiberTotalResponse_xy_eq_regularizedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaFiberAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    massiveDiracStredaFiberTotalResponse data .x .y =
      massiveDiracRegularizedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy occupation := by
  rw [massiveDiracStredaFiberTotalResponse_eq_tracedBastin data .x .y]
  rfl

end

end AnomalousHall.MassiveDirac
