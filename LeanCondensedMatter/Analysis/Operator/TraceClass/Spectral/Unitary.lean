import LeanCondensedMatter.Analysis.Operator.TraceClass.Spectral.Bundled
import LeanCondensedMatter.Analysis.Operator.Unitary

set_option linter.style.header false

/-!
# Unitary conjugation of spectral-trace-class operators

This module contains the spectral summability and trace consequences of the generic bounded-operator
unitary-conjugation API from `Analysis.Operator.Unitary`.
-/

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

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

/-- Spectral trace-class data transports canonically through unitary conjugation. -/
theorem SpectralTraceClass.unitaryConjugate {T : H →L[ℂ] H}
    (hT : SpectralTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    SpectralTraceClass (ContinuousLinearMap.unitaryConjugate U T) := by
  have hcompact : IsCompactOperator (ContinuousLinearMap.unitaryConjugate U T) := by
    change IsCompactOperator (⇑U ∘ ⇑T ∘ ⇑(star U))
    exact (hT.compact.comp_clm (star U)).clm_comp U
  have hsym : (ContinuousLinearMap.unitaryConjugate U T).IsSymmetric := by
    have hself : IsSelfAdjoint T := hT.symmetric.isSelfAdjoint
    change (U ∘SL T ∘SL ContinuousLinearMap.adjoint U).IsSymmetric
    exact (hself.conj_adjoint U).isSymmetric
  exact
    { isTraceClass :=
        (isTraceClass_iff_hasSummableRealEigenvalues hcompact hsym.isSelfAdjoint).2
          (hasSummableRealEigenvalues_unitaryConjugate U T hleft hright hT.summable)
      symmetric := hsym }

/-- The canonical complex trace is invariant under unitary conjugation for bundled
spectral trace-class data. -/
theorem SpectralTraceClass.trace_unitaryConjugate {T : H →L[ℂ] H}
    (hT : SpectralTraceClass T) (U : H →L[ℂ] H)
    (hleft : star U * U = 1) (hright : U * star U = 1) :
    (hT.unitaryConjugate U hleft hright).isTraceClass.trace =
      hT.isTraceClass.trace := by
  rw [(hT.unitaryConjugate U hleft hright).isTraceClass.trace_eq_spectralTrace
      (hT.unitaryConjugate U hleft hright).compact
      (hT.unitaryConjugate U hleft hright).isSelfAdjoint,
    hT.isTraceClass.trace_eq_spectralTrace hT.compact hT.isSelfAdjoint]
  exact_mod_cast ContinuousLinearMap.spectralTrace_unitaryConjugate
    U T hleft hright hT.summable
    (hT.unitaryConjugate U hleft hright).summable

end ContinuousLinearMap
