import LeanCondensedMatter.Transport.Streda.ConductivityMatrix
import LeanCondensedMatter.Transport.Streda.TraceRepresentation

set_option linter.style.header false

/-!
# Shared-provenance traced Středa conductivity matrices

A conductivity matrix should not be assembled from unrelated scalar Středa representations. This
module keeps the Hamiltonian, current family, broadening, energy interval, occupation, and occupation
derivative common to every matrix component, while retaining the pair-dependent analytic proofs
needed by `TracedStredaAnalyticData`.

The resulting matrix is therefore one regularized Středa calculation evaluated on a family of
current vertices. Its Fermi-sea antisymmetry follows from the exact traced residual-sea kernel
antisymmetry, rather than being supplied independently.
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
structure TracedStredaMatrixAnalyticData
    (hamiltonian : H →L[ℂ] H)
    (current : ι → H →L[ℂ] H)
    (broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) where
  /-- Analytic Středa data for each measured/source current pair under the shared setup. -/
  pairData : ∀ i j,
    TracedStredaAnalyticData
      hamiltonian (current i) (current j)
      broadening lowerEnergy upperEnergy occupation occupationDerivative

namespace TracedStredaMatrixAnalyticData

variable {hamiltonian : H →L[ℂ] H}
variable {current : ι → H →L[ℂ] H}
variable {broadening lowerEnergy upperEnergy : ℝ}
variable {occupation occupationDerivative : ℝ → ℂ}

/-- Fermi-surface conductivity matrix extracted from the shared traced Středa data. -/
noncomputable def fermiSurfaceMatrix
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) : ι → ι → ℂ :=
  fun i j =>
    regularizedStredaFermiSurface
      (data.pairData i j).toRegularizedStredaIntegralData

/-- Fermi-sea conductivity matrix extracted from the shared traced Středa data. -/
noncomputable def fermiSeaMatrix
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) : ι → ι → ℂ :=
  fun i j =>
    regularizedStredaFermiSea
      (data.pairData i j).toRegularizedStredaIntegralData

/-- The integrated Fermi-sea matrix remains antisymmetric because the occupation and integration
window are common to every component and the traced residual-sea kernel is pointwise
antisymmetric. -/
theorem fermiSeaMatrix_swap
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative)
    (i j : ι) :
    data.fermiSeaMatrix i j = -data.fermiSeaMatrix j i := by
  unfold fermiSeaMatrix regularizedStredaFermiSea
    TracedStredaAnalyticData.toRegularizedStredaIntegralData
  calc
    (∫ energy in lowerEnergy..upperEnergy,
      occupation energy *
        regularizedStredaResidualSeaTraceKernel
          hamiltonian (current i) (current j) energy broadening) =
      ∫ energy in lowerEnergy..upperEnergy,
        -(occupation energy *
          regularizedStredaResidualSeaTraceKernel
            hamiltonian (current j) (current i) energy broadening) := by
        apply intervalIntegral.integral_congr
        intro energy _
        rw [regularizedStredaResidualSeaTraceKernel_swap]
        ring
    _ = -(∫ energy in lowerEnergy..upperEnergy,
        occupation energy *
          regularizedStredaResidualSeaTraceKernel
            hamiltonian (current j) (current i) energy broadening) := by
      rw [intervalIntegral.integral_neg]

/-- Static Středa conductivity matrix associated with one shared traced analytic setup. -/
noncomputable def toStaticStredaConductivityMatrix
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative) :
    StaticStredaConductivityMatrix ι where
  fermiSurface := data.fermiSurfaceMatrix
  fermiSea := data.fermiSeaMatrix
  fermiSea_swap := data.fermiSeaMatrix_swap

/-- The complete matrix component is exactly the canonical traced Bastin energy integral for the
same ordered current pair and shared physical/analytic setup. -/
theorem toStaticStredaConductivityMatrix_total_eq_tracedBastin
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative)
    (i j : ι) :
    data.toStaticStredaConductivityMatrix.total i j =
      regularizedTracedBastinEnergyIntegral
        hamiltonian (current i) (current j) broadening
        lowerEnergy upperEnergy occupation := by
  unfold toStaticStredaConductivityMatrix StaticStredaConductivityMatrix.total
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

/-- The diagonal traced Bastin response is the longitudinal component of the shared Středa matrix. -/
theorem toStaticStredaConductivityMatrix_longitudinal_eq_tracedBastin
    (data : TracedStredaMatrixAnalyticData hamiltonian current broadening
      lowerEnergy upperEnergy occupation occupationDerivative)
    (i : ι) :
    data.toStaticStredaConductivityMatrix.longitudinal i =
      regularizedTracedBastinEnergyIntegral
        hamiltonian (current i) (current i) broadening
        lowerEnergy upperEnergy occupation := by
  unfold StaticStredaConductivityMatrix.longitudinal
  exact data.toStaticStredaConductivityMatrix_total_eq_tracedBastin i i

end TracedStredaMatrixAnalyticData

end
end Transport
end QuantumTheory
