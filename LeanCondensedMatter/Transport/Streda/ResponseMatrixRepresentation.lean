import LeanCondensedMatter.Transport.Streda.ResponseMatrix
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Shared-provenance traced Středa response matrices

A response matrix should not be assembled from unrelated scalar Středa representations. This module
keeps the Hamiltonian, current family, broadening, energy interval, occupation, and occupation
derivative common to every matrix component, while retaining the pair-dependent analytic proofs
needed by `TracedStredaAnalyticData`.

The resulting matrix is one regularized Středa calculation evaluated on a family of current
vertices. Its Fermi-sea antisymmetry follows from the exact traced residual-sea kernel antisymmetry,
rather than being supplied independently. No physical conductivity normalization is introduced
here.
-/

namespace QuantumTheory
namespace Transport

open MeasureTheory

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Pairwise traced Středa analytic data with one shared physical/analytic setup.

All matrix entries use the same Hamiltonian, current family, finite broadening, energy interval,
occupation, and occupation derivative. Only the proofs needed to validate each ordered current pair
are stored componentwise. -/
structure TracedStredaResponseMatrixAnalyticData
    (hamiltonian : H →L[ℂ] H)
    (current : ι → H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) where
  /-- Analytic Středa data for each measured/source current pair under the shared setup. -/
  pairData : ∀ i j,
    TracedStredaAnalyticData
      hamiltonian (current i) (current j)
      broadening lowerEnergy upperEnergy occupation occupationDerivative

namespace TracedStredaResponseMatrixAnalyticData

variable {hamiltonian : H →L[ℂ] H}
variable {current : ι → H →L[ℂ] H}
variable {broadening lowerEnergy upperEnergy : ℝ}
variable {occupation occupationDerivative : ℝ → ℂ}

/-- Fermi-surface response matrix extracted from the shared traced Středa data. -/
noncomputable def fermiSurfaceMatrix
    (data : TracedStredaResponseMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) : ι → ι → ℂ :=
  fun i j =>
    regularizedStredaFermiSurface
      (data.pairData i j).toRegularizedStredaIntegralData

/-- Fermi-sea response matrix extracted from the shared traced Středa data. -/
noncomputable def fermiSeaMatrix
    (data : TracedStredaResponseMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) : ι → ι → ℂ :=
  fun i j =>
    regularizedStredaFermiSea
      (data.pairData i j).toRegularizedStredaIntegralData

/-- The integrated Fermi-sea matrix remains antisymmetric because the occupation and integration
window are common to every component and the traced residual-sea kernel is pointwise
antisymmetric. -/
theorem fermiSeaMatrix_swap
    (data : TracedStredaResponseMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative)
    (i j : ι) :
    data.fermiSeaMatrix i j = -data.fermiSeaMatrix j i := by
  unfold fermiSeaMatrix regularizedStredaFermiSea
    TracedStredaAnalyticData.toRegularizedStredaIntegralData
  simp_rw [regularizedStredaResidualSeaTraceKernel_swap, mul_neg]
  rw [intervalIntegral.integral_neg]

/-- Static Středa response matrix associated with one shared traced analytic setup. -/
noncomputable def toStaticStredaResponseMatrix
    (data : TracedStredaResponseMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) :
    StaticStredaResponseMatrix ι where
  fermiSurface := data.fermiSurfaceMatrix
  fermiSea := data.fermiSeaMatrix
  fermiSea_swap := data.fermiSeaMatrix_swap

/-- The complete response-matrix component is exactly the canonical traced Bastin energy integral
for the same ordered current pair and shared physical/analytic setup. -/
theorem toStaticStredaResponseMatrix_total_eq_tracedBastin
    (data : TracedStredaResponseMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative)
    (i j : ι) :
    data.toStaticStredaResponseMatrix.total i j =
      regularizedTracedBastinEnergyIntegral
        hamiltonian (current i) (current j) broadening
        lowerEnergy upperEnergy occupation := by
  unfold toStaticStredaResponseMatrix StaticStredaResponseMatrix.total
    fermiSurfaceMatrix fermiSeaMatrix
  calc
    regularizedStredaFermiSurface
          (data.pairData i j).toRegularizedStredaIntegralData +
        regularizedStredaFermiSea
          (data.pairData i j).toRegularizedStredaIntegralData =
      regularizedBastinEnergyIntegral
        (data.pairData i j).toRegularizedStredaIntegralData :=
      (regularizedBastinEnergyIntegral_eq_surface_add_sea
        (data.pairData i j).toRegularizedStredaIntegralData).symm
    _ = regularizedTracedBastinEnergyIntegral
        hamiltonian (current i) (current j) broadening
        lowerEnergy upperEnergy occupation :=
      (data.pairData i j).regularizedBastinEnergyIntegral_eq_traced

end TracedStredaResponseMatrixAnalyticData

end
end Transport
end QuantumTheory
