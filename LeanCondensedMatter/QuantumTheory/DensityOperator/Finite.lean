import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.DensityOperator.Purity
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-dimensional density-operator specialization

Finite dimensionality does not introduce a second density-state type. This module collects the
bridges from the canonical dimension-independent `DensityOperator` API to ordinary finite matrix
traces and finite-index corollaries.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Construct the canonical density state from a positive finite-dimensional trace-one operator. -/
noncomputable def DensityOperator.ofFiniteDimensional
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) : DensityOperator H := by
  have hsymm : ρ.IsSymmetric := hpos.isSelfAdjoint.isSymmetric
  have hcompact : IsCompactOperator ρ :=
    isCompactOperator_of_locallyCompactSpace_dom ρ
  letI : Finite (EigenvectorIndex ρ) :=
    (orthonormal_eigenvectorFamily hcompact hsymm).linearIndependent.finite
  have hsummable : HasSummableRealEigenvalues ρ := Summable.of_finite
  let hstc : SpectralTraceClass ρ :=
    SpectralTraceClass.ofPositive hcompact hpos hsummable
  refine
    { op := ρ
      pos := hpos
      isTraceClass := hstc.isTraceClass
      trace_eq_one := ?_ }
  rw [hstc.isTraceClass.trace_eq_spectralTrace hstc.isSelfAdjoint]
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    hsymm.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ H)) :
      ρ (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i := by
    change (ρ : H →ₗ[ℂ] H) (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i
    simpa [b] using hsymm.apply_eigenvectorBasis rfl i
  have hsum := (hstc.hasSum_diagonalExpectationValue b.toHilbertBasis).tsum_eq
  rw [tsum_fintype] at hsum
  have heigenComplex :
      ((∑ i, hsymm.eigenvalues rfl i : ℝ) : ℂ) =
        LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) :=
    (hsymm.trace_eq_sum_eigenvalues (hn := rfl)).symm
  rw [htrace] at heigenComplex
  have heigen : ∑ i, hsymm.eigenvalues rfl i = 1 := by
    exact_mod_cast heigenComplex
  have hspectral : spectralTrace ρ = 1 := by
    calc
      spectralTrace ρ = ∑ i, diagonalExpectationValue ρ hstc.isSelfAdjoint (b i) := by
        simpa using hsum.symm
      _ = ∑ i, hsymm.eigenvalues rfl i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Complex.ofReal_injective
        rw [coe_diagonalExpectationValue_right, hb i, inner_smul_right,
          inner_self_eq_norm_sq_to_K, b.norm_eq_one]
        simp
      _ = 1 := heigen
  exact_mod_cast hspectral

@[simp]
theorem DensityOperator.ofFiniteDimensional_op
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) :
    (DensityOperator.ofFiniteDimensional ρ hpos htrace).op = ρ :=
  rfl

/-- In finite dimensions, the canonical expectation agrees with the ordinary linear-map trace. -/
theorem DensityOperator.expectation_eq_linearMap_trace (ρ : DensityOperator H)
    (A : H →L[ℂ] H) :
    ρ.expectation A =
      LinearMap.trace ℂ H ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    ρ.isSymmetric.eigenvectorBasis rfl
  rw [ρ.expectation_apply,
    (ρ.isTraceClass.comp_right A).trace_eq_seriesWrt b.toHilbertBasis]
  unfold traceSeriesWrt
  rw [tsum_fintype]
  symm
  simpa [ContinuousLinearMap.mul_def] using
    (LinearMap.trace_eq_sum_inner
      ((ρ.op ∘L A : H →L[ℂ] H) : H →ₗ[ℂ] H) b)

/-- In finite dimensions, the ordinary trace of a density operator is one. -/
theorem DensityOperator.linearMap_trace_eq_one (ρ : DensityOperator H) :
    LinearMap.trace ℂ H (ρ.op : H →ₗ[ℂ] H) = 1 := by
  have h := (ρ.expectation_eq_linearMap_trace (ContinuousLinearMap.id ℂ H)).symm.trans
    ρ.expectation_id
  simpa using h

omit [FiniteDimensional ℂ H] in
/-- A finite diagonal expectation is the finite-index corollary of the countable Hilbert-basis
formula; no separate finite-dimensional hypothesis is needed once the finite basis is supplied. -/
theorem DensityOperator.expectation_eq_sum_diagonal {ι : Type*} [Fintype ι]
    (ρ : DensityOperator H) (A : H →L[ℂ] H) (b : OrthonormalBasis ι ℂ H)
    (w : ι → ℝ) (hρ : ∀ i, (ρ.op : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i) :
    ρ.expectation A = ∑ i, (w i : ℂ) * inner ℂ (b i) (A (b i)) := by
  simpa [tsum_fintype] using
    ρ.expectation_eq_tsum_diagonal A b.toHilbertBasis w (fun i => by simpa using hρ i)

/-- In finite dimensions, the ordinary matrix trace `Tr(ρ²)` is the complex embedding of purity. -/
theorem DensityOperator.linearMap_trace_sq_eq_purity (ρ : DensityOperator H) :
    LinearMap.trace ℂ H
      ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = (purity ρ : ℂ) := by
  calc
    LinearMap.trace ℂ H
        ((ρ.op ∘L ρ.op : H →L[ℂ] H) : H →ₗ[ℂ] H) = ρ.expectation ρ.op :=
      (ρ.expectation_eq_linearMap_trace ρ.op).symm
    _ = (purity ρ : ℂ) := ρ.expectation_op

end QuantumTheory
