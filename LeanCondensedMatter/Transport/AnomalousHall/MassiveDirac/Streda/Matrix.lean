import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.Streda.MatrixRepresentation

set_option linter.style.header false

/-!
# Massive-Dirac static Středa conductivity matrix

This module packages the two in-plane charge-current directions of the clean massive-Dirac model
into the shared-provenance static Středa matrix. Every matrix component therefore uses the same
Hamiltonian, finite broadening, energy interval, occupation, and occupation derivative.

The matrix is the common source for longitudinal and Hall projections. This does not identify the
Středa surface/sea split with intrinsic/extrinsic anomalous-Hall mechanisms.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Shared analytic Středa data for all `x/y` current pairs of one massive-Dirac momentum fiber. -/
abbrev MassiveDiracStredaMatrixAnalyticData
    (e v m px py broadening lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ) :=
  TracedStredaMatrixAnalyticData
    (hamiltonianOperator v m px py)
    (fun direction => currentOperator direction e v)
    broadening lowerEnergy upperEnergy occupation occupationDerivative

/-- Static conductivity matrix for one massive-Dirac momentum fiber under one shared Středa setup. -/
noncomputable def massiveDiracStaticStredaConductivityMatrix
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaMatrixAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    StaticStredaConductivityMatrix Direction2 :=
  data.toStaticStredaConductivityMatrix

/-- Every massive-Dirac matrix entry is the traced Bastin integral for the corresponding pair of
physical charge-current directions under the same analytic setup. -/
theorem massiveDiracStaticStredaConductivityMatrix_total_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaMatrixAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (measured source : Direction2) :
    (massiveDiracStaticStredaConductivityMatrix data).total measured source =
      regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator measured e v) (currentOperator source e v)
        broadening lowerEnergy upperEnergy occupation := by
  simpa [massiveDiracStaticStredaConductivityMatrix] using
    data.toStaticStredaConductivityMatrix_total_eq_tracedBastin measured source

/-- The longitudinal response is the diagonal component of the same massive-Dirac Středa matrix. -/
theorem massiveDiracStaticStredaConductivityMatrix_longitudinal_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaMatrixAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative)
    (direction : Direction2) :
    (massiveDiracStaticStredaConductivityMatrix data).longitudinal direction =
      regularizedTracedBastinEnergyIntegral
        (hamiltonianOperator v m px py)
        (currentOperator direction e v) (currentOperator direction e v)
        broadening lowerEnergy upperEnergy occupation := by
  simpa [massiveDiracStaticStredaConductivityMatrix] using
    data.toStaticStredaConductivityMatrix_longitudinal_eq_tracedBastin direction

/-- The in-plane Hall response is the antisymmetric `x-y` projection of the same matrix. -/
theorem massiveDiracStaticStredaConductivityMatrix_hall_xy_eq_tracedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaMatrixAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    (massiveDiracStaticStredaConductivityMatrix data).hallComponent .x .y =
      (regularizedTracedBastinEnergyIntegral
          (hamiltonianOperator v m px py)
          (currentOperator .x e v) (currentOperator .y e v)
          broadening lowerEnergy upperEnergy occupation -
        regularizedTracedBastinEnergyIntegral
          (hamiltonianOperator v m px py)
          (currentOperator .y e v) (currentOperator .x e v)
          broadening lowerEnergy upperEnergy occupation) / 2 := by
  unfold StaticStredaConductivityMatrix.hallComponent
  rw [massiveDiracStaticStredaConductivityMatrix_total_eq_tracedBastin data .x .y,
    massiveDiracStaticStredaConductivityMatrix_total_eq_tracedBastin data .y .x]

/-- The historical `x-y` scalar Bastin response is the `x-y` entry of the new matrix. -/
theorem massiveDiracStaticStredaConductivityMatrix_total_xy_eq_regularizedBastin
    {e v m px py broadening lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (data : MassiveDiracStredaMatrixAnalyticData
      e v m px py broadening lowerEnergy upperEnergy occupation occupationDerivative) :
    (massiveDiracStaticStredaConductivityMatrix data).total .x .y =
      massiveDiracRegularizedBastinEnergyIntegral
        e v m px py broadening lowerEnergy upperEnergy occupation := by
  rw [massiveDiracStaticStredaConductivityMatrix_total_eq_tracedBastin data .x .y]
  rfl

end

end AnomalousHall.MassiveDirac
