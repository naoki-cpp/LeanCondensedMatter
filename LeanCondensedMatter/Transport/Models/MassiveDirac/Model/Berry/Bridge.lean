import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral.BerryPointwise

set_option linter.style.header false

/-!
# Force-matrix / Berry-curvature bridge for the massive Dirac model

The model layer owns the gauge-independent two-band force-matrix numerator and interband energy gap.
This file identifies their Hall combination with the closed massive-Dirac Berry-curvature benchmark.
For target band `n` and opposite band `m`,

```text
Im Tr(P_m vₓ P_n vᵧ) = -s m v² / E,
E_n - E_m = 2 s E,
```

so the two-band force-matrix curvature reduces to `-s m v² / (2 E³)`.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open BerryGeometry
open QuantumTheory.Transport

/-- The gauge-independent interband force numerator is exactly the product of the corresponding
generic Hamiltonian-derivative matrix elements. -/
theorem forceMatrixTraceNumerator_eq_hamiltonianDerivativeMatrixElements
    (μ ν : Fin 2) (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    forceMatrixTraceNumerator μ ν band v m px py =
      (pointwiseEigenbasisData v m px py hE).hamiltonianDerivativeMatrixElement
          μ (oppositeBand band) band *
        (pointwiseEigenbasisData v m px py hE).hamiltonianDerivativeMatrixElement
          ν band (oppositeBand band) := by
  let data := pointwiseEigenbasisData v m px py hE
  let opposite := data.eigenbasis (oppositeBand band)
  let current := data.eigenbasis band
  have htrace :
      forceMatrixTraceNumerator μ ν band v m px py =
        finiteDimensionalOperatorTrace
          (bandProjectorOperator (oppositeBand band) v m px py * velocityOperator μ v *
            bandProjectorOperator band v m px py * velocityOperator ν v) := by
    symm
    simpa [forceMatrixTraceNumerator, bandProjectorOperator, velocityOperator, matrixOperator] using
      finiteDimensionalOperatorTrace_toEuclideanCLM
        (bandProjector (oppositeBand band) v m px py * velocity μ v *
          bandProjector band v m px py * velocity ν v)
  rw [htrace]
  rw [bandProjectorOperator_eq_rankOne_pointwiseEigenbasis
      (oppositeBand band) v m px py hE]
  rw [bandProjectorOperator_eq_rankOne_pointwiseEigenbasis band v m px py hE]
  change
    finiteDimensionalOperatorTrace
        (InnerProductSpace.rankOne ℂ opposite opposite * velocityOperator μ v *
          InnerProductSpace.rankOne ℂ current current * velocityOperator ν v) =
      inner ℂ opposite (velocityOperator μ v current) *
        inner ℂ current (velocityOperator ν v opposite)
  rw [show
      InnerProductSpace.rankOne ℂ opposite opposite * velocityOperator μ v *
            InnerProductSpace.rankOne ℂ current current * velocityOperator ν v =
        (inner ℂ opposite (velocityOperator μ v current)) •
          InnerProductSpace.rankOne ℂ opposite
            ((velocityOperator ν v).adjoint current) by
      simp [ContinuousLinearMap.mul_def, InnerProductSpace.comp_rankOne,
        InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_inner_left]]
  simp [finiteDimensionalOperatorTrace_apply, InnerProductSpace.trace_rankOne,
    ContinuousLinearMap.adjoint_inner_left]

/-- The real two-band force-matrix Berry-curvature expression obtained from the Hall component of
the generic formula `2 Im(Fˣ_mn Fʸ_nm)/(E_n-E_m)²` after using that the energy denominator is real. -/
def forceMatrixBerryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  2 * (forceMatrixTraceNumerator 0 1 band v m px py).im /
    interbandEnergyGap band v m px py ^ 2

/-- The projector/force-matrix expression equals the closed massive-Dirac Berry curvature away
from the band degeneracy. -/
theorem forceMatrixBerryCurvature_eq_berryCurvature (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    forceMatrixBerryCurvature band v m px py = berryCurvature band v m px py := by
  rw [forceMatrixBerryCurvature, forceMatrixTraceNumerator_xy_eq band v m px py hE,
    interbandEnergyGap_eq]
  simp only [Complex.sub_im, Complex.neg_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  cases band <;>
    simp [berryCurvature_upper, berryCurvature_lower] <;>
    field_simp [hE]

end

end QuantumTheory.Transport.Models.MassiveDirac
