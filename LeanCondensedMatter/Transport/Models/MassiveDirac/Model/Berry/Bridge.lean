import LeanCondensedMatter.Analysis.Operator.Spectral.BerryCurvature
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral

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

private theorem diracHilbert_finrank :
    Module.finrank ℂ DiracHilbert = 2 := by
  simp [DiracHilbert]

private noncomputable def diracEigenvaluesFin (v m px py : ℝ) : Fin 2 → ℝ :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues
    diracHilbert_finrank

private noncomputable def diracEigenbasisFin (v m px py : ℝ) :
    OrthonormalBasis (Fin 2) ℂ DiracHilbert :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvectorBasis
    diracHilbert_finrank

private theorem diracEigenvalue_sq (v m px py : ℝ) (i : Fin 2) :
    diracEigenvaluesFin v m px py i ^ 2 = energySq v m px py := by
  let b := diracEigenbasisFin v m px py
  let lam := diracEigenvaluesFin v m px py i
  have heig :
      hamiltonianOperator v m px py (b i) = (((lam : ℝ) : ℂ)) • b i := by
    exact
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank i
  have happly := congrArg
    (fun T : DiracHilbert →L[ℂ] DiracHilbert => T (b i))
    (hamiltonianOperator_mul_self v m px py)
  change hamiltonianOperator v m px py (hamiltonianOperator v m px py (b i)) =
    (((energySq v m px py : ℝ) : ℂ)) • b i at happly
  rw [heig, map_smul, heig, smul_smul] at happly
  have hinner := congrArg (fun x : DiracHilbert => inner ℂ (b i) x) happly
  simp only [inner_smul_right, b.inner_eq_one, mul_one] at hinner
  have hreal : lam * lam = energySq v m px py := by exact_mod_cast hinner
  simpa [lam, pow_two] using hreal

private theorem diracEigenvalues_sum_eq_zero (v m px py : ℝ) :
    diracEigenvaluesFin v m px py 0 + diracEigenvaluesFin v m px py 1 = 0 := by
  let hsym := (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric
  have htrace :
      LinearMap.trace ℂ DiracHilbert
          (hamiltonianOperator v m px py : DiracHilbert →ₗ[ℂ] DiracHilbert) = 0 := by
    change finiteDimensionalOperatorTrace (hamiltonianOperator v m px py) = 0
    rw [show finiteDimensionalOperatorTrace (hamiltonianOperator v m px py) =
        Matrix.trace (hamiltonian v m px py) by
      simpa [hamiltonianOperator, matrixOperator] using
        finiteDimensionalOperatorTrace_toEuclideanCLM (hamiltonian v m px py)]
    simp [hamiltonian_eq_pauliCombination]
  have hsumComplex :
      (((∑ i : Fin 2, hsym.eigenvalues diracHilbert_finrank i : ℝ) : ℂ)) =
        LinearMap.trace ℂ DiracHilbert
          (hamiltonianOperator v m px py : DiracHilbert →ₗ[ℂ] DiracHilbert) :=
    (hsym.trace_eq_sum_eigenvalues (hn := diracHilbert_finrank)).symm
  rw [htrace] at hsumComplex
  have hsumReal :
      ∑ i : Fin 2, hsym.eigenvalues diracHilbert_finrank i = 0 := by
    exact_mod_cast hsumComplex
  simpa [diracEigenvaluesFin, hsym] using hsumReal

private theorem diracEigenvalue_zero_eq_energy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    diracEigenvaluesFin v m px py 0 = energy v m px py := by
  have horder :
      diracEigenvaluesFin v m px py 1 ≤ diracEigenvaluesFin v m px py 0 :=
    (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues_antitone
      diracHilbert_finrank (by norm_num)
  have hsum := diracEigenvalues_sum_eq_zero v m px py
  have hsq := diracEigenvalue_sq v m px py 0
  have hEsq := energy_sq v m px py
  have hEpos : 0 < energy v m px py :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hE)
  nlinarith

private theorem diracEigenvalue_one_eq_neg_energy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    diracEigenvaluesFin v m px py 1 = -energy v m px py := by
  have hsum := diracEigenvalues_sum_eq_zero v m px py
  rw [diracEigenvalue_zero_eq_energy v m px py hE] at hsum
  linarith

private theorem diracEigenvaluesFin_ne_of_ne
    (left right : Fin 2) (v m px py : ℝ) (hE : energy v m px py ≠ 0)
    (hne : left ≠ right) :
    diracEigenvaluesFin v m px py left ≠ diracEigenvaluesFin v m px py right := by
  have h01 :
      diracEigenvaluesFin v m px py 0 ≠ diracEigenvaluesFin v m px py 1 := by
    rw [diracEigenvalue_zero_eq_energy v m px py hE,
      diracEigenvalue_one_eq_neg_energy v m px py hE]
    intro h
    apply hE
    linarith
  fin_cases left <;> fin_cases right
  · exact (hne rfl).elim
  · simpa using h01
  · simpa using h01.symm
  · exact (hne rfl).elim

private def bandIndex : Band → Fin 2
  | .lower => 1
  | .upper => 0

/-- Generic pointwise spectral/Berry data for the nondegenerate massive-Dirac Hamiltonian.

The generic spectral index remains Mathlib's native `Fin 2`; physical `Band` labels are identified
only by the bridge theorems below. The two derivative directions are the physical momentum
directions. This is a pointwise local construction only: it makes no global smooth-gauge,
Berry-phase, Chern-number, or topology claim. -/
noncomputable def pointwiseBerryData
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    PointwiseEigenbasisData (Fin 2) (Fin 2) DiracHilbert :=
  PointwiseEigenbasisData.ofNondegenerateEigenbasis
    (hamiltonianOperator v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    (diracEigenbasisFin v m px py)
    (diracEigenvaluesFin v m px py)
    (fun i =>
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank i)
    (fun direction => velocityOperator direction v)
    (fun direction => velocityOperator_isSelfAdjoint direction v)
    (fun left right hne => diracEigenvaluesFin_ne_of_ne left right v m px py hE hne)

/-- The generic spectral index attached to a physical band has the model band energy. -/
@[simp] theorem pointwiseBerryData_energy_bandIndex
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy (bandIndex band) =
      bandEnergy band v m px py := by
  unfold pointwiseBerryData PointwiseEigenbasisData.ofNondegenerateEigenbasis
  cases band
  · exact diracEigenvalue_one_eq_neg_energy v m px py hE
  · exact diracEigenvalue_zero_eq_energy v m px py hE

@[simp] theorem pointwiseBerryData_hamiltonianDerivative
    (direction : Fin 2) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivative direction =
      velocityOperator direction v := rfl

/-- The generic opposite-band level spacing is the model interband gap. -/
theorem pointwiseBerryData_interbandEnergyGap
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy (bandIndex band) -
        (pointwiseBerryData v m px py hE).energy (bandIndex (oppositeBand band)) =
      interbandEnergyGap band v m px py := by
  rw [pointwiseBerryData_energy_bandIndex, pointwiseBerryData_energy_bandIndex]
  rfl

private theorem bandProjectorOperator_eq_pointwise_spectral_formula
    (band : Band) (v m px py : ℝ) :
    bandProjectorOperator band v m px py =
      (1 / 2 : ℂ) •
        ((1 : DiracHilbert →L[ℂ] DiracHilbert) +
          (((bandSign band / energy v m px py : ℝ) : ℂ)) •
            hamiltonianOperator v m px py) := by
  unfold bandProjectorOperator bandProjector hamiltonianOperator matrixOperator
  simp [map_add, map_smul]

private theorem bandProjectorOperator_apply_diracEigenbasisFin
    (projected : Band) (source : Fin 2) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjectorOperator projected v m px py
        (diracEigenbasisFin v m px py source) =
      if bandIndex projected = source then diracEigenbasisFin v m px py source else 0 := by
  let b := diracEigenbasisFin v m px py
  have hEc : (((energy v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hE
  have heig :
      hamiltonianOperator v m px py (b source) =
        (((diracEigenvaluesFin v m px py source : ℝ) : ℂ)) • b source := by
    exact
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank source
  rw [bandProjectorOperator_eq_pointwise_spectral_formula]
  rw [smul_apply, add_apply, one_apply_eq_self, smul_apply, heig, smul_smul]
  have hfactor :
      (1 / 2 : ℂ) •
          (b source +
            (((bandSign projected / energy v m px py : ℝ) : ℂ) *
              ((diracEigenvaluesFin v m px py source : ℝ) : ℂ)) • b source) =
        ((1 / 2 : ℂ) *
          (1 + (((bandSign projected / energy v m px py : ℝ) : ℂ)) *
            (((diracEigenvaluesFin v m px py source : ℝ) : ℂ)))) • b source := by
    module
  rw [hfactor]
  have hcoeff :
      (1 / 2 : ℂ) *
          (1 + (((bandSign projected / energy v m px py : ℝ) : ℂ)) *
            (((diracEigenvaluesFin v m px py source : ℝ) : ℂ))) =
        if bandIndex projected = source then 1 else 0 := by
    cases projected <;> fin_cases source <;>
      simp [bandIndex, bandSign,
        diracEigenvalue_zero_eq_energy v m px py hE,
        diracEigenvalue_one_eq_neg_energy v m px py hE, hE] <;>
      field_simp [hEc] <;>
      ring
  rw [hcoeff]
  split <;> simp [b]

private theorem bandProjectorOperator_eq_rankOne
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator band v m px py =
      InnerProductSpace.rankOne ℂ
        (diracEigenbasisFin v m px py (bandIndex band))
        (diracEigenbasisFin v m px py (bandIndex band)) := by
  let b := diracEigenbasisFin v m px py
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro source
  change
    bandProjectorOperator band v m px py (b source) =
      InnerProductSpace.rankOne ℂ (b (bandIndex band)) (b (bandIndex band)) (b source)
  rw [bandProjectorOperator_apply_diracEigenbasisFin band source v m px py hE]
  cases band <;> fin_cases source <;>
    simp [b, bandIndex, InnerProductSpace.rankOne_apply]

/-- The sole opposite-band generic force-matrix product is the model projector trace. -/
theorem pointwiseBerryData_forceMatrixElement_product
    (μ ν : Fin 2) (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivativeMatrixElement
          μ (bandIndex (oppositeBand band)) (bandIndex band) *
        (pointwiseBerryData v m px py hE).hamiltonianDerivativeMatrixElement
          ν (bandIndex band) (bandIndex (oppositeBand band)) =
      forceMatrixTraceNumerator μ ν band v m px py := by
  let b := diracEigenbasisFin v m px py
  change
    inner ℂ (b (bandIndex (oppositeBand band))) (velocityOperator μ v (b (bandIndex band))) *
        inner ℂ (b (bandIndex band))
          (velocityOperator ν v (b (bandIndex (oppositeBand band)))) =
      forceMatrixTraceNumerator μ ν band v m px py
  rw [show
      forceMatrixTraceNumerator μ ν band v m px py =
        finiteDimensionalOperatorTrace
          (bandProjectorOperator (oppositeBand band) v m px py *
            velocityOperator μ v *
            bandProjectorOperator band v m px py *
            velocityOperator ν v) by
    unfold forceMatrixTraceNumerator
    symm
    simpa [bandProjectorOperator, velocityOperator, matrixOperator] using
      finiteDimensionalOperatorTrace_toEuclideanCLM
        (bandProjector (oppositeBand band) v m px py * velocity μ v *
          bandProjector band v m px py * velocity ν v)]
  rw [bandProjectorOperator_eq_rankOne (oppositeBand band) v m px py hE,
    bandProjectorOperator_eq_rankOne band v m px py hE,
    finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner
      (((InnerProductSpace.rankOne ℂ
          (b (bandIndex (oppositeBand band))) (b (bandIndex (oppositeBand band)))) *
        velocityOperator μ v *
        (InnerProductSpace.rankOne ℂ (b (bandIndex band)) (b (bandIndex band))) *
        velocityOperator ν v : DiracHilbert →L[ℂ] DiracHilbert) :
        DiracHilbert →ₗ[ℂ] DiracHilbert) b,
    Fin.sum_univ_two]
  cases band <;>
    simp [b, bandIndex, InnerProductSpace.rankOne_apply, map_smul,
      inner_smul_right, mul_comm, mul_assoc]

/-- The real two-band force-matrix Berry-curvature expression obtained from the Hall component of
the generic formula `2 Im(Fˣ_mn Fʸ_nm)/(E_n-E_m)²` after using that the energy denominator is real. -/
def forceMatrixBerryCurvature (band : Band) (v m px py : ℝ) : ℝ :=
  2 * (forceMatrixTraceNumerator 0 1 band v m px py).im /
    interbandEnergyGap band v m px py ^ 2

private theorem two_mul_product_div_real_im
    (z w : ℂ) (gap : ℝ) (hgap : gap ≠ 0) :
    2 * ((z / (gap : ℂ)) * (w / (gap : ℂ))).im =
      2 * (z * w).im / gap ^ 2 := by
  have hgapc : (gap : ℂ) ≠ 0 := by exact_mod_cast hgap
  have hcancel :
      ((z / (gap : ℂ)) * (w / (gap : ℂ))) * (((gap ^ 2 : ℝ) : ℂ)) =
        z * w := by
    push_cast
    field_simp [hgapc]
  have him := congrArg Complex.im hcancel
  rw [Complex.mul_im] at him
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
  apply (eq_div_iff (pow_ne_zero 2 hgap)).2
  calc
    2 * ((z / (gap : ℂ)) * (w / (gap : ℂ))).im * gap ^ 2 =
        2 * (((z / (gap : ℂ)) * (w / (gap : ℂ))).im * gap ^ 2) := by ring
    _ = 2 * (z * w).im := by rw [him]

/-- The generic pointwise Berry curvature is the model force-matrix curvature. -/
theorem pointwiseBerryCurvature_eq_forceMatrixBerryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).berryCurvature 0 1 (bandIndex band) =
      forceMatrixBerryCurvature band v m px py := by
  let data := pointwiseBerryData v m px py hE
  have hself :
      ∀ direction, IsSelfAdjoint (data.hamiltonianDerivative direction) := by
    intro direction
    exact velocityOperator_isSelfAdjoint direction v
  have hnondegenerate :
      ∀ other, other ≠ bandIndex band →
        data.energy other ≠ data.energy (bandIndex band) := by
    intro other hother
    change
      diracEigenvaluesFin v m px py other ≠
        diracEigenvaluesFin v m px py (bandIndex band)
    exact diracEigenvaluesFin_ne_of_ne other (bandIndex band) v m px py hE hother
  rw [data.berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements
    0 1 (bandIndex band) hself hnondegenerate]
  have hgap := interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hforce := pointwiseBerryData_forceMatrixElement_product 0 1 band v m px py hE
  change
    data.hamiltonianDerivativeMatrixElement 0
        (bandIndex (oppositeBand band)) (bandIndex band) *
      data.hamiltonianDerivativeMatrixElement 1
        (bandIndex band) (bandIndex (oppositeBand band)) =
      forceMatrixTraceNumerator 0 1 band v m px py at hforce
  cases band
  · simp [bandIndex, oppositeBand] at hforce
    simp only [bandIndex, Fin.sum_univ_two,
      if_neg (show (0 : Fin 2) ≠ 1 by decide), if_pos rfl, add_zero]
    rw [show
      data.energy 1 - data.energy 0 =
        interbandEnergyGap Band.lower v m px py by
      simpa [bandIndex] using
        pointwiseBerryData_interbandEnergyGap Band.lower v m px py hE]
    rw [two_mul_product_div_real_im _ _ _ hgap, hforce]
    rfl
  · simp [bandIndex, oppositeBand] at hforce
    simp only [bandIndex, Fin.sum_univ_two,
      if_pos rfl, if_neg (show (1 : Fin 2) ≠ 0 by decide), zero_add]
    rw [show
      data.energy 0 - data.energy 1 =
        interbandEnergyGap Band.upper v m px py by
      simpa [bandIndex] using
        pointwiseBerryData_interbandEnergyGap Band.upper v m px py hE]
    rw [two_mul_product_div_real_im _ _ _ hgap, hforce]
    rfl

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

/-- Canonical specialization of generic pointwise curvature to the closed massive-Dirac benchmark. -/
theorem pointwiseBerryCurvature_eq_berryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).berryCurvature 0 1 (bandIndex band) =
      berryCurvature band v m px py :=
  (pointwiseBerryCurvature_eq_forceMatrixBerryCurvature band v m px py hE).trans
    (forceMatrixBerryCurvature_eq_berryCurvature band v m px py hE)

end

end QuantumTheory.Transport.Models.MassiveDirac
