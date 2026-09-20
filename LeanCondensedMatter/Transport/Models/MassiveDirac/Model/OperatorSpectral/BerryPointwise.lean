import LeanCondensedMatter.Analysis.Operator.Spectral.BerryConnection
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.OperatorSpectral
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option linter.style.header false

/-!
# Pointwise Berry spectral data for the massive-Dirac model

This file connects the nondegenerate massive-Dirac Hamiltonian to the generic pointwise Berry
eigenbasis API. The construction uses Mathlib's finite-dimensional spectral theorem and only
relabels its sorted eigenbasis by the physical two-band index.

At a fixed momentum with `E ≠ 0`, the sorted eigenvalues are `+E` then `-E`, so the resulting
basis is indexed by `Band.upper` and `Band.lower`. The Hamiltonian derivatives supplied to the
generic adapter are exactly the two model velocity operators.

This is pointwise spectral data only. No global eigenvector gauge, Brillouin-zone patching, or
topological claim is made here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open BerryGeometry

private theorem diracHilbert_finrank : Module.finrank ℂ DiracHilbert = 2 := by
  simp [DiracHilbert]

private noncomputable def sortedEigenvalues (v m px py : ℝ) : Fin 2 → ℝ :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvalues diracHilbert_finrank

private noncomputable def sortedEigenbasis (v m px py : ℝ) :
    OrthonormalBasis (Fin 2) ℂ DiracHilbert :=
  (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.eigenvectorBasis
    diracHilbert_finrank

private theorem bandEnergy_hasEigenvalue
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    Module.End.HasEigenvalue
      (hamiltonianOperator v m px py : DiracHilbert →ₗ[ℂ] DiracHilbert)
      ((bandEnergy band v m px py : ℝ) : ℂ) := by
  have hPne := bandProjectorOperator_ne_zero band v m px py
  obtain ⟨x, hx⟩ : ∃ x : DiracHilbert, bandProjectorOperator band v m px py x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hPne
    ext x
    exact h x
  apply Module.End.hasEigenvalue_of_hasEigenvector
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    have happ := congrArg
      (fun T : DiracHilbert →L[ℂ] DiracHilbert => T x)
      (hamiltonianOperator_mul_bandProjectorOperator band v m px py hE)
    simpa using happ
  · exact hx

private theorem sortedEigenvalues_eq_bandEnergy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    sortedEigenvalues v m px py 0 = bandEnergy .upper v m px py ∧
      sortedEigenvalues v m px py 1 = bandEnergy .lower v m px py := by
  let hsymm := (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric
  obtain ⟨iu, hiu⟩ :=
    hsymm.exists_eigenvalues_eq diracHilbert_finrank
      (bandEnergy_hasEigenvalue .upper v m px py hE)
  obtain ⟨il, hil⟩ :=
    hsymm.exists_eigenvalues_eq diracHilbert_finrank
      (bandEnergy_hasEigenvalue .lower v m px py hE)
  have hiuR :
      sortedEigenvalues v m px py iu = bandEnergy .upper v m px py := by
    change ((sortedEigenvalues v m px py iu : ℝ) : ℂ) =
      ((bandEnergy .upper v m px py : ℝ) : ℂ) at hiu
    exact_mod_cast hiu
  have hilR :
      sortedEigenvalues v m px py il = bandEnergy .lower v m px py := by
    change ((sortedEigenvalues v m px py il : ℝ) : ℂ) =
      ((bandEnergy .lower v m px py : ℝ) : ℂ) at hil
    exact_mod_cast hil
  have hEpos : 0 < energy v m px py :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hE)
  have hanti : Antitone (sortedEigenvalues v m px py) := by
    exact hsymm.eigenvalues_antitone diracHilbert_finrank
  fin_cases iu <;> fin_cases il
  · exfalso
    simp [bandEnergy] at hiuR hilR
    apply hE
    linarith
  · exact ⟨hiuR, hilR⟩
  · exfalso
    have horder :
        sortedEigenvalues v m px py (1 : Fin 2) ≤
          sortedEigenvalues v m px py (0 : Fin 2) :=
      hanti (by decide)
    rw [hiuR, hilR] at horder
    simp [bandEnergy] at horder
    linarith
  · exfalso
    simp [bandEnergy] at hiuR hilR
    apply hE
    linarith

private def finTwoEquivBand : Fin 2 ≃ Band where
  toFun := Fin.cases .upper (fun _ => .lower)
  invFun
    | .upper => 0
    | .lower => 1
  left_inv i := by
    fin_cases i <;> rfl
  right_inv band := by
    cases band <;> rfl

private noncomputable def bandEigenbasis (v m px py : ℝ) :
    OrthonormalBasis Band ℂ DiracHilbert :=
  (sortedEigenbasis v m px py).reindex finTwoEquivBand

private theorem hamiltonianOperator_bandEigenbasis
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) (band : Band) :
    hamiltonianOperator v m px py (bandEigenbasis v m px py band) =
      ((bandEnergy band v m px py : ℝ) : ℂ) • bandEigenbasis v m px py band := by
  have hspectral := sortedEigenvalues_eq_bandEnergy v m px py hE
  have happ := (hamiltonianOperator_isSelfAdjoint v m px py).isSymmetric.apply_eigenvectorBasis
    diracHilbert_finrank
  cases band with
  | lower =>
      simpa [bandEigenbasis, sortedEigenbasis, sortedEigenvalues, finTwoEquivBand, hspectral.2]
        using happ (1 : Fin 2)
  | upper =>
      simpa [bandEigenbasis, sortedEigenbasis, sortedEigenvalues, finTwoEquivBand, hspectral.1]
        using happ (0 : Fin 2)

/-- Generic pointwise Berry eigenbasis data for the nondegenerate massive-Dirac Hamiltonian.

The band index is the physical `Band` type, the energy field is `bandEnergy`, and the two
Hamiltonian-derivative directions are exactly the bounded velocity operators. -/
noncomputable def pointwiseEigenbasisData
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    PointwiseEigenbasisData (Fin 2) Band DiracHilbert :=
  PointwiseEigenbasisData.ofSimpleSpectrum
    (hamiltonianOperator v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    (bandEigenbasis v m px py)
    (fun band => bandEnergy band v m px py)
    (hamiltonianOperator_bandEigenbasis v m px py hE)
    (fun direction => velocityOperator direction v)
    (fun direction => velocityOperator_isSelfAdjoint direction v)
    (bandEnergy_injective v m px py hE)

@[simp] theorem pointwiseEigenbasisData_energy
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) (band : Band) :
    (pointwiseEigenbasisData v m px py hE).energy band =
      bandEnergy band v m px py := rfl

@[simp] theorem pointwiseEigenbasisData_hamiltonianDerivative
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) (direction : Fin 2) :
    (pointwiseEigenbasisData v m px py hE).hamiltonianDerivative direction =
      velocityOperator direction v := rfl

end

end QuantumTheory.Transport.Models.MassiveDirac
