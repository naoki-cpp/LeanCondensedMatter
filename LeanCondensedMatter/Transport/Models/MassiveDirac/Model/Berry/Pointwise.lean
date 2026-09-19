import LeanCondensedMatter.Analysis.Operator.Spectral.BerryCurvature
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Interband
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral

set_option linter.style.header false

/-!
# Pointwise generic Berry data for the massive-Dirac model

This module specializes the generic finite-dimensional pointwise Berry-geometry API to the
nondegenerate two-band massive-Dirac Hamiltonian.  The construction is pointwise in momentum:
it chooses the finite-dimensional spectral eigenbasis at the selected momentum, fixes the
first-order eigenvector derivatives by the off-diagonal Born--Fock coefficients, and uses the
physical velocity operators as the two Hamiltonian derivatives.

The adapter is available only under the explicit nondegeneracy hypothesis
`energy v m px py ≠ 0`.  It makes no global smooth-gauge, Brillouin-zone, Berry-phase, Chern-number,
or topology claim.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport
open BerryGeometry

private theorem diracHilbert_finrank :
    Module.finrank ℂ DiracHilbert = 2 := by
  simp [DiracHilbert]

private def finTwoEquivBand : Fin 2 ≃ Band where
  toFun i := if i = 0 then .upper else .lower
  invFun
    | .upper => 0
    | .lower => 1
  left_inv i := by
    fin_cases i <;> simp
  right_inv band := by
    cases band <;> simp

private theorem velocityOperator_isSelfAdjoint
    (direction : Fin 2) (v : ℝ) :
    IsSelfAdjoint (velocityOperator direction v) := by
  have h := currentOperator_isSelfAdjoint direction (-1) v
  simpa [currentOperator_eq_charge_smul_velocityOperator] using h

private noncomputable def diracEigenvaluesFin (v m px py : ℝ) : Fin 2 → ℝ :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues
    diracHilbert_finrank

private noncomputable def diracEigenbasisFin (v m px py : ℝ) :
    OrthonormalBasis (Fin 2) ℂ DiracHilbert :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvectorBasis
    diracHilbert_finrank

/-- The pointwise massive-Dirac eigenbasis indexed by physical lower/upper band labels.

Mathlib orders the finite-dimensional self-adjoint eigenbasis by decreasing eigenvalue, so the
`Fin 2` basis is reindexed by `0 ↦ upper`, `1 ↦ lower`.  The identification with the signed
massive-Dirac band energies is proved below under nondegeneracy. -/
noncomputable def pointwiseEigenbasis (v m px py : ℝ) :
    OrthonormalBasis Band ℂ DiracHilbert :=
  (diracEigenbasisFin v m px py).reindex finTwoEquivBand

private theorem hamiltonianOperator_mul_self
    (v m px py : ℝ) :
    hamiltonianOperator v m px py * hamiltonianOperator v m px py =
      (((energy v m px py ^ 2 : ℝ) : ℂ)) •
        (1 : DiracHilbert →L[ℂ] DiracHilbert) := by
  have h := congrArg matrixOperator (hamiltonian_mul_self v m px py)
  simpa [hamiltonianOperator, matrixOperator, ← energy_sq] using h

private theorem hamiltonianOperator_trace_eq_zero
    (v m px py : ℝ) :
    LinearMap.trace ℂ DiracHilbert
        (hamiltonianOperator v m px py : DiracHilbert →ₗ[ℂ] DiracHilbert) = 0 := by
  change finiteDimensionalOperatorTrace (hamiltonianOperator v m px py) = 0
  rw [show
      finiteDimensionalOperatorTrace (hamiltonianOperator v m px py) =
        Matrix.trace (hamiltonian v m px py) by
    simpa [hamiltonianOperator, matrixOperator] using
      finiteDimensionalOperatorTrace_toEuclideanCLM (hamiltonian v m px py)]
  simp [hamiltonian_eq_pauliCombination]

private theorem diracEigenvalue_sq
    (v m px py : ℝ) (i : Fin 2) :
    diracEigenvaluesFin v m px py i ^ 2 = energy v m px py ^ 2 := by
  let b := diracEigenbasisFin v m px py
  let lam := diracEigenvaluesFin v m px py i
  have heig :
      hamiltonianOperator v m px py (b i) =
        (((lam : ℝ) : ℂ)) • b i := by
    change
      hamiltonianOperator v m px py
          (diracEigenbasisFin v m px py i) =
        (((diracEigenvaluesFin v m px py i : ℝ) : ℂ)) •
          diracEigenbasisFin v m px py i
    exact
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank i
  have hop := hamiltonianOperator_mul_self v m px py
  have happly := congrArg
    (fun T : DiracHilbert →L[ℂ] DiracHilbert => T (b i)) hop
  change
      hamiltonianOperator v m px py
          (hamiltonianOperator v m px py (b i)) =
        (((energy v m px py ^ 2 : ℝ) : ℂ)) • b i at happly
  rw [heig, map_smul, heig, smul_smul] at happly
  have hinner := congrArg (fun x : DiracHilbert => inner ℂ (b i) x) happly
  simp only [inner_smul_right, b.inner_eq_one, mul_one] at hinner
  have hreal : lam ^ 2 = energy v m px py ^ 2 := by
    exact_mod_cast hinner
  simpa [lam] using hreal

private theorem diracEigenvalues_sum_eq_zero
    (v m px py : ℝ) :
    diracEigenvaluesFin v m px py 0 + diracEigenvaluesFin v m px py 1 = 0 := by
  let hsym := (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric
  have hsumComplex :
      (((∑ i : Fin 2, hsym.eigenvalues diracHilbert_finrank i : ℝ) : ℂ)) =
        LinearMap.trace ℂ DiracHilbert
          (hamiltonianOperator v m px py : DiracHilbert →ₗ[ℂ] DiracHilbert) :=
    (hsym.trace_eq_sum_eigenvalues (hn := diracHilbert_finrank)).symm
  rw [hamiltonianOperator_trace_eq_zero] at hsumComplex
  have hsumReal :
      ∑ i : Fin 2, hsym.eigenvalues diracHilbert_finrank i = 0 := by
    exact_mod_cast hsumComplex
  simpa [diracEigenvaluesFin, hsym] using hsumReal

private theorem diracEigenvalue_zero_eq_energy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    diracEigenvaluesFin v m px py 0 = energy v m px py := by
  have horder :
      diracEigenvaluesFin v m px py 1 ≤ diracEigenvaluesFin v m px py 0 := by
    exact
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues_antitone
        diracHilbert_finrank (by norm_num)
  have hsum := diracEigenvalues_sum_eq_zero v m px py
  have hsq := diracEigenvalue_sq v m px py 0
  have hEnonneg : 0 ≤ energy v m px py := Real.sqrt_nonneg _
  have hEpos : 0 < energy v m px py := lt_of_le_of_ne hEnonneg (Ne.symm hE)
  nlinarith

private theorem diracEigenvalue_one_eq_neg_energy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    diracEigenvaluesFin v m px py 1 = -energy v m px py := by
  have hsum := diracEigenvalues_sum_eq_zero v m px py
  rw [diracEigenvalue_zero_eq_energy v m px py hE] at hsum
  linarith

/-- The reindexed spectral basis carries exactly the signed massive-Dirac band energies away from
the Dirac degeneracy. -/
theorem hamiltonianOperator_pointwiseEigenbasis
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py (pointwiseEigenbasis v m px py band) =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        pointwiseEigenbasis v m px py band := by
  cases band
  · change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 1) =
        (((-energy v m px py : ℝ) : ℂ)) • diracEigenbasisFin v m px py 1
    have heig :=
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank (1 : Fin 2)
    rw [show
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues
          diracHilbert_finrank (1 : Fin 2) =
        -energy v m px py by
      exact diracEigenvalue_one_eq_neg_energy v m px py hE] at heig
    exact heig
  · change
      hamiltonianOperator v m px py (diracEigenbasisFin v m px py 0) =
        (((energy v m px py : ℝ) : ℂ)) • diracEigenbasisFin v m px py 0
    have heig :=
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
        diracHilbert_finrank (0 : Fin 2)
    rw [show
      (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues
          diracHilbert_finrank (0 : Fin 2) =
        energy v m px py by
      exact diracEigenvalue_zero_eq_energy v m px py hE] at heig
    exact heig

private noncomputable def pointwiseForceMatrixElement
    (direction : Fin 2) (target source : Band) (v m px py : ℝ) : ℂ :=
  inner ℂ (pointwiseEigenbasis v m px py target)
    (velocityOperator direction v (pointwiseEigenbasis v m px py source))

private theorem star_pointwiseForceMatrixElement
    (direction : Fin 2) (target source : Band) (v m px py : ℝ) :
    (starRingEnd ℂ) (pointwiseForceMatrixElement direction target source v m px py) =
      pointwiseForceMatrixElement direction source target v m px py := by
  calc
    (starRingEnd ℂ) (pointwiseForceMatrixElement direction target source v m px py) =
        inner ℂ
          (velocityOperator direction v (pointwiseEigenbasis v m px py source))
          (pointwiseEigenbasis v m px py target) := by
      simp [pointwiseForceMatrixElement, inner_conj_symm]
    _ = inner ℂ (pointwiseEigenbasis v m px py source)
        (velocityOperator direction v (pointwiseEigenbasis v m px py target)) := by
      exact (velocityOperator_isSelfAdjoint direction v).isSymmetric.apply_clm _ _
    _ = pointwiseForceMatrixElement direction source target v m px py := rfl

private theorem pointwiseForceMatrixElement_diagonal_im_eq_zero
    (direction : Fin 2) (band : Band) (v m px py : ℝ) :
    (pointwiseForceMatrixElement direction band band v m px py).im = 0 := by
  have h := congrArg Complex.im
    (star_pointwiseForceMatrixElement direction band band v m px py)
  simp at h
  linarith

private theorem pointwiseForceMatrixElement_diagonal_ofReal_re
    (direction : Fin 2) (band : Band) (v m px py : ℝ) :
    (((pointwiseForceMatrixElement direction band band v m px py).re : ℝ) : ℂ) =
      pointwiseForceMatrixElement direction band band v m px py := by
  apply Complex.ext
  · simp
  · simp [pointwiseForceMatrixElement_diagonal_im_eq_zero]

private noncomputable def pointwiseEigenvectorDerivative
    (direction : Fin 2) (band : Band) (v m px py : ℝ) : DiracHilbert :=
  (pointwiseForceMatrixElement direction (oppositeBand band) band v m px py /
      (((interbandEnergyGap band v m px py : ℝ) : ℂ))) •
    pointwiseEigenbasis v m px py (oppositeBand band)

private def pointwiseEnergyDerivative
    (direction : Fin 2) (band : Band) (v m px py : ℝ) : ℝ :=
  (pointwiseForceMatrixElement direction band band v m px py).re

private theorem star_pointwiseEigenvectorDerivativeCoefficient
    (direction : Fin 2) (band : Band) (v m px py : ℝ) :
    (starRingEnd ℂ)
        (pointwiseForceMatrixElement direction (oppositeBand (oppositeBand band))
            (oppositeBand band) v m px py /
          (((interbandEnergyGap (oppositeBand band) v m px py : ℝ) : ℂ))) =
      -(pointwiseForceMatrixElement direction (oppositeBand band) band v m px py /
          (((interbandEnergyGap band v m px py : ℝ) : ℂ))) := by
  rw [oppositeBand_oppositeBand, map_div,
    star_pointwiseForceMatrixElement]
  simp [interbandEnergyGap_oppositeBand]

private theorem pointwiseForceMatrixElement_offdiag_coefficient
    (direction : Fin 2) (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    pointwiseForceMatrixElement direction (oppositeBand band) band v m px py +
        (pointwiseForceMatrixElement direction (oppositeBand band) band v m px py /
            (((interbandEnergyGap band v m px py : ℝ) : ℂ))) *
          (((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ)) =
      (((bandEnergy band v m px py : ℝ) : ℂ)) *
        (pointwiseForceMatrixElement direction (oppositeBand band) band v m px py /
          (((interbandEnergyGap band v m px py : ℝ) : ℂ))) := by
  have hgap :
      interbandEnergyGap band v m px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hgapc : (((interbandEnergyGap band v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hgap
  rw [interbandEnergyGap] at hgapc ⊢
  field_simp [hgapc]
  ring_nf

private theorem pointwiseDifferentiatedEigenpair
    (direction : Fin 2) (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    velocityOperator direction v (pointwiseEigenbasis v m px py band) +
        hamiltonianOperator v m px py
          (pointwiseEigenvectorDerivative direction band v m px py) =
      (((pointwiseEnergyDerivative direction band v m px py : ℝ) : ℂ)) •
          pointwiseEigenbasis v m px py band +
        (((bandEnergy band v m px py : ℝ) : ℂ)) •
          pointwiseEigenvectorDerivative direction band v m px py := by
  let b := pointwiseEigenbasis v m px py
  let Fnn := pointwiseForceMatrixElement direction band band v m px py
  let Fmn := pointwiseForceMatrixElement direction (oppositeBand band) band v m px py
  let gap : ℂ := (((interbandEnergyGap band v m px py : ℝ) : ℂ))
  have hdecomp := b.sum_repr'
    (velocityOperator direction v (b band))
  have hsum :
      (∑ i : Band,
          inner ℂ (b i) (velocityOperator direction v (b band)) • b i) =
        Fnn • b band + Fmn • b (oppositeBand band) := by
    cases band <;>
      simp [sum_band, Fnn, Fmn, b, pointwiseForceMatrixElement, add_comm]
  rw [hsum] at hdecomp
  have hdiag :
      (((pointwiseEnergyDerivative direction band v m px py : ℝ) : ℂ)) = Fnn := by
    simpa [pointwiseEnergyDerivative, Fnn] using
      pointwiseForceMatrixElement_diagonal_ofReal_re direction band v m px py
  have hoff :=
    pointwiseForceMatrixElement_offdiag_coefficient
      direction band v m px py hE
  change
    velocityOperator direction v (b band) +
        hamiltonianOperator v m px py ((Fmn / gap) • b (oppositeBand band)) =
      (((pointwiseEnergyDerivative direction band v m px py : ℝ) : ℂ)) • b band +
        (((bandEnergy band v m px py : ℝ) : ℂ)) •
          ((Fmn / gap) • b (oppositeBand band))
  rw [map_smul,
    hamiltonianOperator_pointwiseEigenbasis (oppositeBand band) v m px py hE]
  rw [← hdecomp, hdiag]
  change
    Fnn • b band + Fmn • b (oppositeBand band) +
        (Fmn / gap) •
          ((((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ)) •
            b (oppositeBand band)) =
      Fnn • b band +
        (((bandEnergy band v m px py : ℝ) : ℂ)) •
          ((Fmn / gap) • b (oppositeBand band))
  have hoff' :
      Fmn +
          (Fmn / gap) *
            (((bandEnergy (oppositeBand band) v m px py : ℝ) : ℂ)) =
        (((bandEnergy band v m px py : ℝ) : ℂ)) * (Fmn / gap) := by
    simpa [Fmn, gap] using hoff
  rw [smul_smul, smul_smul, add_assoc, ← add_smul, hoff']

private theorem pointwiseDifferentiatedOrthonormality
    (direction : Fin 2) (left right : Band) (v m px py : ℝ) :
    inner ℂ (pointwiseEigenvectorDerivative direction left v m px py)
        (pointwiseEigenbasis v m px py right) +
      inner ℂ (pointwiseEigenbasis v m px py left)
        (pointwiseEigenvectorDerivative direction right v m px py) = 0 := by
  let b := pointwiseEigenbasis v m px py
  have horth := b.orthonormal
  cases left <;> cases right
  · simp only [pointwiseEigenvectorDerivative, inner_smul_left, inner_smul_right]
    rw [horth.inner_eq_zero (by decide), horth.inner_eq_zero (by decide)]
    simp
  · simp only [pointwiseEigenvectorDerivative, inner_smul_left, inner_smul_right]
    rw [b.inner_eq_one, b.inner_eq_one,
      star_pointwiseEigenvectorDerivativeCoefficient direction Band.upper v m px py]
    simp
  · simp only [pointwiseEigenvectorDerivative, inner_smul_left, inner_smul_right]
    rw [b.inner_eq_one, b.inner_eq_one,
      star_pointwiseEigenvectorDerivativeCoefficient direction Band.lower v m px py]
    simp
  · simp only [pointwiseEigenvectorDerivative, inner_smul_left, inner_smul_right]
    rw [horth.inner_eq_zero (by decide), horth.inner_eq_zero (by decide)]
    simp

/-- The massive-Dirac Hamiltonian packaged as the generic pointwise Berry-geometry data at a
nondegenerate momentum point.

The two derivative directions are the physical momentum directions, so
`hamiltonianDerivative μ = velocityOperator μ v`.  The derivative-state gauge is fixed only at
this point by setting its band-diagonal component to zero and its off-diagonal component to the
Born--Fock coefficient. -/
noncomputable def pointwiseBerryData
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    PointwiseEigenbasisData (Fin 2) Band DiracHilbert where
  hamiltonian := hamiltonianOperator v m px py
  hamiltonian_selfAdjoint := hamiltonianOperator_isSelfAdjoint v m px py
  eigenbasis := pointwiseEigenbasis v m px py
  energy := fun band => bandEnergy band v m px py
  hamiltonian_eigenvector := fun band =>
    hamiltonianOperator_pointwiseEigenbasis band v m px py hE
  hamiltonianDerivative := fun direction => velocityOperator direction v
  eigenvectorDerivative := fun direction band =>
    pointwiseEigenvectorDerivative direction band v m px py
  energyDerivative := fun direction band =>
    pointwiseEnergyDerivative direction band v m px py
  differentiatedEigenpair := fun direction band =>
    pointwiseDifferentiatedEigenpair direction band v m px py hE
  differentiatedOrthonormality := fun direction left right =>
    pointwiseDifferentiatedOrthonormality direction left right v m px py

@[simp]
theorem pointwiseBerryData_energy
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy band =
      bandEnergy band v m px py :=
  rfl

@[simp]
theorem pointwiseBerryData_hamiltonianDerivative
    (direction : Fin 2) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivative direction =
      velocityOperator direction v :=
  rfl

@[simp]
theorem pointwiseBerryData_hamiltonianDerivativeMatrixElement
    (direction : Fin 2) (target source : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivativeMatrixElement
        direction target source =
      pointwiseForceMatrixElement direction target source v m px py :=
  rfl

/-- The generic level spacing in the pointwise adapter is the model's interband energy gap. -/
theorem pointwiseBerryData_interbandEnergyGap
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).energy band -
        (pointwiseBerryData v m px py hE).energy (oppositeBand band) =
      interbandEnergyGap band v m px py :=
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

private theorem bandProjectorOperator_apply_pointwiseEigenbasis
    (projected source : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    bandProjectorOperator projected v m px py
        (pointwiseEigenbasis v m px py source) =
      if projected = source then pointwiseEigenbasis v m px py source else 0 := by
  rw [bandProjectorOperator_eq_pointwise_spectral_formula]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply,
    hamiltonianOperator_pointwiseEigenbasis source v m px py hE]
  cases projected <;> cases source <;>
    simp [bandSign, bandEnergy] <;>
    field_simp [hE]

private theorem bandProjectorOperator_apply_eq_inner_smul
    (projected : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) (x : DiracHilbert) :
    bandProjectorOperator projected v m px py x =
      inner ℂ (pointwiseEigenbasis v m px py projected) x •
        pointwiseEigenbasis v m px py projected := by
  let b := pointwiseEigenbasis v m px py
  have hrepr := b.sum_repr' x
  calc
    bandProjectorOperator projected v m px py x =
        bandProjectorOperator projected v m px py
          (∑ source : Band, inner ℂ (b source) x • b source) := by
      rw [hrepr]
    _ = ∑ source : Band,
        inner ℂ (b source) x •
          bandProjectorOperator projected v m px py (b source) := by
      simp [map_sum]
    _ = inner ℂ (b projected) x • b projected := by
      cases projected <;>
        simp [sum_band, b,
          bandProjectorOperator_apply_pointwiseEigenbasis _ _ v m px py hE]

/-- The product of generic Hamiltonian-derivative matrix elements for the sole opposite-band term is
exactly the gauge-independent projector trace used by the massive-Dirac model. -/
theorem pointwiseBerryData_forceMatrixElement_product
    (μ ν : Fin 2) (band : Band) (v m px py : ℝ)
    (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).hamiltonianDerivativeMatrixElement
          μ (oppositeBand band) band *
        (pointwiseBerryData v m px py hE).hamiltonianDerivativeMatrixElement
          ν band (oppositeBand band) =
      forceMatrixTraceNumerator μ ν band v m px py := by
  let b := pointwiseEigenbasis v m px py
  rw [pointwiseBerryData_hamiltonianDerivativeMatrixElement,
    pointwiseBerryData_hamiltonianDerivativeMatrixElement]
  change
    pointwiseForceMatrixElement μ (oppositeBand band) band v m px py *
        pointwiseForceMatrixElement ν band (oppositeBand band) v m px py =
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
  rw [finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner
      ((bandProjectorOperator (oppositeBand band) v m px py *
        velocityOperator μ v *
        bandProjectorOperator band v m px py *
        velocityOperator ν v :
          DiracHilbert →L[ℂ] DiracHilbert) :
        DiracHilbert →ₗ[ℂ] DiracHilbert) b]
  rw [sum_band]
  cases band <;>
    simp [b, bandProjectorOperator_apply_eq_inner_smul,
      pointwiseForceMatrixElement, mul_comm, mul_left_comm, mul_assoc]

private theorem pointwiseBerryData_nondegenerate
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ∀ other, other ≠ band →
      (pointwiseBerryData v m px py hE).energy other ≠
        (pointwiseBerryData v m px py hE).energy band := by
  intro other hother
  cases band <;> cases other
  · exact (hother rfl).elim
  · simp only [pointwiseBerryData_energy, bandEnergy, bandSign]
    intro h
    apply hE
    linarith
  · simp only [pointwiseBerryData_energy, bandEnergy, bandSign]
    intro h
    apply hE
    linarith
  · exact (hother rfl).elim

private theorem pointwiseBerryData_hamiltonianDerivative_selfAdjoint
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    ∀ direction,
      IsSelfAdjoint
        ((pointwiseBerryData v m px py hE).hamiltonianDerivative direction) := by
  intro direction
  exact velocityOperator_isSelfAdjoint direction v

/-- The generic force-matrix curvature of the pointwise adapter is the existing gauge-independent
massive-Dirac projector/force-matrix expression. -/
theorem pointwiseBerryCurvature_eq_forceMatrixBerryCurvature
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (pointwiseBerryData v m px py hE).berryCurvature 0 1 band =
      2 * (forceMatrixTraceNumerator 0 1 band v m px py).im /
        interbandEnergyGap band v m px py ^ 2 := by
  let data := pointwiseBerryData v m px py hE
  rw [data.berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements
    0 1 band
    (pointwiseBerryData_hamiltonianDerivative_selfAdjoint v m px py hE)
    (pointwiseBerryData_nondegenerate band v m px py hE)]
  have hgap :
      interbandEnergyGap band v m px py ≠ 0 :=
    interbandEnergyGap_ne_zero_of_energy_ne_zero band v m px py hE
  have hgapc : (((interbandEnergyGap band v m px py : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hgap
  have hforce :=
    pointwiseBerryData_forceMatrixElement_product 0 1 band v m px py hE
  cases band <;>
    simp [sum_band, data, pointwiseBerryData_interbandEnergyGap,
      oppositeBand, hforce] <;>
    field_simp [hgap, hgapc] <;>
    simp [Complex.mul_im] <;>
    ring

end

end QuantumTheory.Transport.Models.MassiveDirac
