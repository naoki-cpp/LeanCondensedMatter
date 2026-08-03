import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-dimensional density-state construction

A positive finite-dimensional operator whose ordinary trace is one determines the canonical
spectral-trace-class density state. This is a constructor for the standard type, not a parallel
finite-dimensional state model.
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
      spectralTraceClass := hstc
      spectralTrace_eq_one := ?_ }
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
    hsymm.eigenvectorBasis rfl
  have hb (i : Fin (Module.finrank ℂ H)) :
      ρ (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i := by
    change (ρ : H →ₗ[ℂ] H) (b i) = (hsymm.eigenvalues rfl i : ℂ) • b i
    simpa [b] using hsymm.apply_eigenvectorBasis rfl i
  have hsum := (hstc.hasSum_inner_apply b.toHilbertBasis).tsum_eq
  rw [tsum_fintype] at hsum
  calc
    hstc.trace = ∑ i, (inner ℂ (b i) (ρ (b i)) : ℂ).re := by
      simpa using hsum.symm
    _ = ∑ i, hsymm.eigenvalues rfl i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hb i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      simp
    _ = (LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H)).re :=
      (hsymm.re_trace_eq_sum_eigenvalues (hn := rfl)).symm
    _ = 1 := by rw [htrace]; norm_num

@[simp]
theorem DensityOperator.ofFiniteDimensional_op
    (ρ : H →L[ℂ] H) (hpos : ρ.IsPositive)
    (htrace : LinearMap.trace ℂ H (ρ : H →ₗ[ℂ] H) = 1) :
    (DensityOperator.ofFiniteDimensional ρ hpos htrace).op = ρ :=
  rfl

end QuantumTheory
