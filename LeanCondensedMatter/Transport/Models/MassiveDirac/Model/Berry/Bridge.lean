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

private def finTwoEquivBand : Fin 2 ≃ Band where
  toFun i := if i = 0 then .upper else .lower
  invFun
    | .upper => 0
    | .lower => 1
  left_inv i := by fin_cases i <;> simp
  right_inv band := by cases band <;> simp

@[simp] private theorem finTwoEquivBand_symm_lower :
    finTwoEquivBand.symm .lower = 1 := rfl

@[simp] private theorem finTwoEquivBand_symm_upper :
    finTwoEquivBand.symm .upper = 0 := rfl

private noncomputable def diracEigenvaluesFin (v m px py : ℝ) : Fin 2 → ℝ :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues
    diracHilbert_finrank

private noncomputable def diracEigenbasisFin (v m px py : ℝ) :
    OrthonormalBasis (Fin 2) ℂ DiracHilbert :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvectorBasis
    diracHilbert_finrank

private noncomputable def pointwiseEigenbasis (v m px py : ℝ) :
    OrthonormalBasis Band ℂ DiracHilbert :=
  (diracEigenbasisFin v m px py).reindex finTwoEquivBand

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

private theorem hamiltonianOperator_pointwiseEigenbasis
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py (pointwiseEigenbasis v m px py band) =
      (((bandEnergy band v m px py : ℝ) : ℂ)) • pointwiseEigenbasis v m px py band := by
  have hsum := diracEigenvalues_sum_eq_zero v m px py
  have hzero := diracEigenvalue_zero_eq_energy v m px py hE
  have hone : diracEigenvaluesFin v m px py 1 = -energy v m px py := by
    rw [hzero] at hsum
    linarith
  cases band
  · change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 1) =
        (((-energy v m px py : ℝ) : ℂ)) • diracEigenbasisFin v m px py 1
    have heig :=
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank (1 : Fin 2)
    change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 1) =
        (((diracEigenvaluesFin v m px py 1 : ℝ) : ℂ)) •
          diracEigenbasisFin v m px py 1 at heig
    rw [hone] at heig
    exact heig
  · change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 0) =
        (((energy v m px py : ℝ) : ℂ)) • diracEigenbasisFin v m px py 0
    have heig :=
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank (0 : Fin 2)
    change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 0) =
        (((diracEigenvaluesFin v m px py 0 : ℝ) : ℂ)) •
          diracEigenbasisFin v m px py 0 at heig
    rw [hzero] at heig
    exact heig

private theorem bandEnergy_ne_of_ne
    (left right : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0)
    (hne : left ≠ right) :
    bandEnergy left v m px py ≠ bandEnergy right v m px py := by
  cases left <;> cases right
  · exact (hne rfl).elim
  · simp only [bandEnergy, bandSign]
    intro h
    apply hE
    linarith
  · simp only [bandEnergy, bandSign]
    intro h
    apply hE
    linarith
  · exact (hne rfl).elim

/-- Generic pointwise spectral/Berry data for the nondegenerate massive-Dirac Hamiltonian.

The two derivative directions are the physical momentum directions. This is a pointwise local
construction only: it makes no global smooth-gauge, Berry-phase, Chern-number, or topology claim. -/
noncomputable def pointwiseBerryData
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    PointwiseEigenbasisData (Fin 2) Band DiracHilbert :=
  PointwiseEigenbasisData.ofNondegenerateEigenbasis
    (hamiltonianOperator v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    (pointwiseEigenbasis v m px py)
    (fun band => bandEnergy band v m px py)
    (fun band => hamiltonianOperator_pointwiseEigenbasis band v m px py hE)
    (fun direction => velocityOperator direction v)
    (fun direction => velocityOperator_isSelfAdjoint direction v)
    (fun left right hne => bandEnergy_ne_of_ne left right v m px py hE hne)

@[simp] theorem pointwiseBerryData_energy
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy band = bandEnergy band v m px py := rfl

@[simp] theorem pointwiseBerryData_hamiltonianDerivative
    (direction : Fin 2) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivative direction =
      velocityOperator direction v := rfl

/-- The generic opposite-band level spacing is the model interband gap. -/
theorem pointwiseBerryData_interbandEnergyGap
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy band -
        (pointwiseBerryData v m px py hE).energy (oppositeBand band) =
      interbandEnergyGap band v m px py := rfl

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
