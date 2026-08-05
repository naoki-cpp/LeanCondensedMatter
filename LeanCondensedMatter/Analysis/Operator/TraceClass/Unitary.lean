import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option linter.style.header false

/-!
# Unitary conjugation of spectral-trace-class operators

This module provides the algebraic spectral bridge needed to transport density operators under
bounded unitary dynamics.  The hypotheses are stated as the two operator inverse identities, so the
results are reusable independently of any particular unitary bundling.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- The linear equivalence implemented by an operator whose adjoint is a two-sided inverse. -/
noncomputable def unitaryLinearEquiv (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) : H ≃ₗ[ℂ] H where
  toFun := U
  invFun := fun x => (star U) x
  left_inv := fun x => by
    have h := congrArg (fun A : H →L[ℂ] H => A x) hleft
    simpa [mul_apply_eq_comp] using h
  right_inv := fun x => by
    have h := congrArg (fun A : H →L[ℂ] H => A x) hright
    simpa [mul_apply_eq_comp] using h
  map_add' := U.map_add
  map_smul' := U.map_smul

/-- Conjugation of an operator by a unitary representative. -/
noncomputable def unitaryConjugate (U T : H →L[ℂ] H) : H →L[ℂ] H :=
  U * T * star U

/-- Unitary conjugation maps each eigenspace to the corresponding eigenspace with the same
eigenvalue. -/
theorem eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ =
      Submodule.map (unitaryLinearEquiv U hleft hright).toLinearMap
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_map]
    refine ⟨star U x, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change U (T ((star U) x)) = μ • x at hx
      have h := congrArg (fun y : H => (star U) y) hx
      have hcancel : (star U) (U (T ((star U) x))) = T ((star U) x) := by
        have h' := congrArg (fun A : H →L[ℂ] H => A (T ((star U) x))) hleft
        simpa [mul_apply_eq_comp] using h'
      simpa [hcancel, map_smul] using h
    · change U ((star U) x) = x
      have h := congrArg (fun A : H →L[ℂ] H => A x) hright
      simpa [mul_apply_eq_comp] using h
  · intro hx
    rw [Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    change U (T ((star U) (U y))) = μ • U y
    have hcancel : (star U) (U y) = y := by
      have h := congrArg (fun A : H →L[ℂ] H => A y) hleft
      simpa [mul_apply_eq_comp] using h
    rw [hcancel]
    simpa using congrArg (fun z : H => U z) hy

/-- Corresponding eigenspaces have the same finite dimension under unitary conjugation. -/
theorem finrank_eigenspace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) (μ : ℂ) :
    Module.finrank ℂ
        (Module.End.eigenspace ((unitaryConjugate U T : H →L[ℂ] H) : H →ₗ[ℂ] H) μ) =
      Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) := by
  rw [eigenspace_unitaryConjugate U T hleft hright μ]
  exact (unitaryLinearEquiv U hleft hright).finrank_map_eq _

/-- Absolute summability of real eigenvalues with multiplicity is invariant under unitary
conjugation. -/
theorem hasSummableRealEigenvalues_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1)
    (hT : HasSummableRealEigenvalues T) :
    HasSummableRealEigenvalues (unitaryConjugate U T) := by
  have hweighted : Summable (fun μ : {γ : ℝ // γ ≠ 0} =>
      (Module.finrank ℂ
        (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)) : ℝ) * |μ.1|) := by
    have hsig := (summable_sigma_of_nonneg
      (f := fun a : EigenvectorIndex T => |a.1.1|)
      (fun a => abs_nonneg _)).mp hT
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hsig.2
  change Summable (fun a : EigenvectorIndex (unitaryConjugate U T) => |a.1.1|)
  apply (summable_sigma_of_nonneg
    (f := fun a : EigenvectorIndex (unitaryConjugate U T) => |a.1.1|)
    (fun a => abs_nonneg _)).mpr
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, finrank_eigenspace_unitaryConjugate U T hleft hright] using hweighted

/-- The spectral trace is invariant under unitary conjugation. -/
theorem spectralTrace_unitaryConjugate (U T : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1)
    (hT : HasSummableRealEigenvalues T)
    (hconj : HasSummableRealEigenvalues (unitaryConjugate U T)) :
    spectralTrace (unitaryConjugate U T) = spectralTrace T := by
  change (∑' b : EigenvectorIndex (unitaryConjugate U T), b.1.1) =
    ∑' a : EigenvectorIndex T, a.1.1
  rw [tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex hconj),
    tsum_eigenvectorIndex_eq_tsum_mul_finrank (summable_eigenvectorIndex hT)]
  apply tsum_congr
  intro μ
  rw [finrank_eigenspace_unitaryConjugate U T hleft hright]

/-- Compactness is preserved under bounded unitary conjugation. -/
theorem isCompactOperator_unitaryConjugate (U T : H →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (unitaryConjugate U T) := by
  change IsCompactOperator (⇑U ∘ ⇑T ∘ ⇑(star U))
  exact (hT.comp_clm (star U)).clm_comp U

/-- Positivity is preserved under conjugation by any bounded operator. -/
theorem IsPositive.unitaryConjugate {T : H →L[ℂ] H} (hT : T.IsPositive)
    (U : H →L[ℂ] H) : (unitaryConjugate U T).IsPositive := by
  change (U ∘SL T ∘SL ContinuousLinearMap.adjoint U).IsPositive
  exact hT.conj_adjoint U

/-- Spectral trace-class data transports canonically through unitary conjugation. -/
noncomputable def SpectralTraceClass.unitaryConjugate {T : H →L[ℂ] H}
    (hT : SpectralTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    SpectralTraceClass (ContinuousLinearMap.unitaryConjugate U T) where
  compact := isCompactOperator_unitaryConjugate U T hT.compact
  symmetric := by
    have hself : IsSelfAdjoint T := hT.symmetric.isSelfAdjoint
    change (U ∘SL T ∘SL ContinuousLinearMap.adjoint U).IsSymmetric
    exact (hself.conj_adjoint U).isSymmetric
  summable := hasSummableRealEigenvalues_unitaryConjugate U T hleft hright hT.summable

@[simp]
theorem SpectralTraceClass.trace_unitaryConjugate {T : H →L[ℂ] H}
    (hT : SpectralTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    (hT.unitaryConjugate U hleft hright).trace = hT.trace := by
  rw [(hT.unitaryConjugate U hleft hright).trace_eq_spectralTrace,
    hT.trace_eq_spectralTrace]
  exact ContinuousLinearMap.spectralTrace_unitaryConjugate
    U T hleft hright hT.summable
    (hT.unitaryConjugate U hleft hright).summable

end ContinuousLinearMap
