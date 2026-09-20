import LeanCondensedMatter.Analysis.Operator.Spectral.BerryCurvature
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

/-- The generic band-energy difference to the opposite band is the model interband gap. -/
theorem pointwiseEigenbasisData_energy_sub_oppositeBand_eq_interbandEnergyGap
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).energy band -
        (pointwiseEigenbasisData v m px py hE).energy (oppositeBand band) =
      interbandEnergyGap band v m px py := rfl

private theorem mul_div_real_gap_im
    (a b : ℂ) (gap : ℝ) (hgap : gap ≠ 0) :
    ((a / ((gap : ℝ) : ℂ)) * (b / ((gap : ℝ) : ℂ))).im =
      (a * b).im / gap ^ 2 := by
  have hcoeff :
      (((((gap : ℝ) : ℂ))⁻¹) ^ 2) =
        ((((gap⁻¹ ^ 2 : ℝ) : ℂ))) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_pow]
  calc
    ((a / ((gap : ℝ) : ℂ)) * (b / ((gap : ℝ) : ℂ))).im =
        (((((gap : ℝ) : ℂ))⁻¹) ^ 2 * (a * b)).im := by
      congr 1
      simp only [div_eq_mul_inv]
      ring
    _ = ((((gap⁻¹ ^ 2 : ℝ) : ℂ)) * (a * b)).im := by rw [hcoeff]
    _ = (a * b).im / gap ^ 2 := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul]
      field_simp [hgap]
      ring

/-- The generic pointwise Berry curvature in the physical x-y directions is exactly the
model projector/force-matrix curvature away from the Dirac degeneracy. -/
theorem pointwiseBerryCurvature_xy_eq_forceMatrixBerryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).berryCurvature 0 1 band =
      forceMatrixBerryCurvature band v m px py := by
  classical
  let data := pointwiseEigenbasisData v m px py hE
  have hself : ∀ direction, IsSelfAdjoint (data.hamiltonianDerivative direction) := by
    intro direction
    change IsSelfAdjoint (velocityOperator direction v)
    exact velocityOperator_isSelfAdjoint direction v
  have hnondegenerate :
      ∀ source, source ≠ band → data.energy source ≠ data.energy band := by
    intro source hsource hsame
    apply hsource
    apply bandEnergy_injective v m px py hE
    change bandEnergy source v m px py = bandEnergy band v m px py at hsame
    exact hsame
  unfold forceMatrixBerryCurvature
  rw [forceMatrixTraceNumerator_eq_hamiltonianDerivativeMatrixElements
    0 1 band v m px py hE]
  change data.berryCurvature 0 1 band =
    2 * (data.hamiltonianDerivativeMatrixElement 0 (oppositeBand band) band *
      data.hamiltonianDerivativeMatrixElement 1 band (oppositeBand band)).im /
        interbandEnergyGap band v m px py ^ 2
  have hgapEq :
      data.energy band - data.energy (oppositeBand band) =
        interbandEnergyGap band v m px py := by
    change
      (pointwiseEigenbasisData v m px py hE).energy band -
          (pointwiseEigenbasisData v m px py hE).energy (oppositeBand band) =
        interbandEnergyGap band v m px py
    exact pointwiseEigenbasisData_energy_sub_oppositeBand_eq_interbandEnergyGap
      band v m px py hE
  have hgap : data.energy band - data.energy (oppositeBand band) ≠ 0 := by
    rw [hgapEq]
    exact interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  rw [data.berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements
    0 1 band hself hnondegenerate]
  rw [sum_band]
  cases band with
  | lower =>
      simp only [reduceCtorEq, ↓reduceIte, oppositeBand_lower, zero_add]
      have hgapLower : data.energy .lower - data.energy .upper ≠ 0 := by
        simpa only [oppositeBand_lower] using hgap
      have hgapEqLower :
          data.energy .lower - data.energy .upper =
            interbandEnergyGap .lower v m px py := by
        simpa only [oppositeBand_lower] using hgapEq
      rw [mul_div_real_gap_im _ _ _ hgapLower, hgapEqLower]
      ring
  | upper =>
      simp only [reduceCtorEq, ↓reduceIte, oppositeBand_upper, add_zero]
      have hgapUpper : data.energy .upper - data.energy .lower ≠ 0 := by
        simpa only [oppositeBand_upper] using hgap
      have hgapEqUpper :
          data.energy .upper - data.energy .lower =
            interbandEnergyGap .upper v m px py := by
        simpa only [oppositeBand_upper] using hgapEq
      rw [mul_div_real_gap_im _ _ _ hgapUpper, hgapEqUpper]
      ring

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

/-- Canonical specialization from the generic pointwise Berry curvature to the closed
massive-Dirac formula. -/
theorem pointwiseBerryCurvature_xy_eq_berryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).berryCurvature 0 1 band =
      berryCurvature band v m px py := by
  rw [pointwiseBerryCurvature_xy_eq_forceMatrixBerryCurvature band v m px py hE,
    forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE]

/-- Reversing the two physical momentum directions gives the negative closed curvature, inherited
from generic Berry-curvature antisymmetry. -/
theorem pointwiseBerryCurvature_yx_eq_neg_berryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).berryCurvature 1 0 band =
      -berryCurvature band v m px py := by
  rw [(pointwiseEigenbasisData v m px py hE).berryCurvature_swap 0 1 band,
    pointwiseBerryCurvature_xy_eq_berryCurvature band v m px py hE]

/-- Generic upper-band x-y curvature in the repository sign convention. -/
theorem pointwiseBerryCurvature_xy_upper
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).berryCurvature 0 1 .upper =
      -(m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  rw [pointwiseBerryCurvature_xy_eq_berryCurvature .upper v m px py hE,
    berryCurvature_upper]

/-- Generic lower-band x-y curvature in the repository sign convention. -/
theorem pointwiseBerryCurvature_xy_lower
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseEigenbasisData v m px py hE).berryCurvature 0 1 .lower =
      (m * v ^ 2) / (2 * energy v m px py ^ 3) := by
  rw [pointwiseBerryCurvature_xy_eq_berryCurvature .lower v m px py hE,
    berryCurvature_lower]

end

end QuantumTheory.Transport.Models.MassiveDirac
