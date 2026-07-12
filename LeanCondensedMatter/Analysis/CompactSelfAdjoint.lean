import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A countable orthonormal family of eigenvectors for a compact self-adjoint operator

Mathlib's spectral theorem for compact self-adjoint operators (`Mathlib.Analysis.
InnerProductSpace.Spectrum`) only proves qualitative facts about eigenspaces as submodules
(`orthogonalComplement_iSup_eigenspaces_eq_bot`, `finite_dimensional_eigenspace`) — it never
packages these into an actual countable indexed orthonormal family of eigenvectors. This file
takes the first step towards Track C's trace-class operator theory
(`notes/roadmaps/operator-algebra.md`) by building that family, gluing together an orthonormal
basis of each nonzero eigenspace via `OrthogonalFamily.orthonormal_sigma_orthonormal`.

**Scope note:** the eigenvalue-`0` eigenspace (the kernel of `T`) is deliberately excluded from
the family — it contributes nothing to the trace regardless of its (possibly infinite, even
non-separable) dimension, so restricting to nonzero eigenvalues keeps the index type free of
that complication. See `notes/caveats.md` for what remains: countability of the index type
(from compactness) and the `tsum` reconstruction of `T` from this family, neither proved here.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The index type gluing together an orthonormal basis of each nonzero eigenspace of `T`: a
nonzero real eigenvalue `μ`, together with an index into a chosen orthonormal basis of the
(finite-dimensional, for `μ ≠ 0`) eigenspace `eigenspace T μ`. -/
def EigenvectorIndex (T : H →L[ℂ] H) : Type :=
  Σ μ : { μ : ℝ // μ ≠ 0 }, Fin (Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)))

/-- The orthonormal family of eigenvectors of `T`, glued from an orthonormal basis of each
nonzero eigenspace. -/
noncomputable def eigenvectorFamily (hT : IsCompactOperator T) :
    EigenvectorIndex T → H :=
  fun a =>
    haveI := finite_dimensional_eigenspace hT (a.1.1 : ℂ) (by exact_mod_cast a.1.2)
    ((stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ))) a.2 : H)

theorem orthonormal_eigenvectorFamily (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    Orthonormal ℂ (eigenvectorFamily hT) := by
  have hOrth : OrthogonalFamily ℂ (fun μ : ℝ => Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ))
      (fun μ => (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ)).subtypeₗᵢ) :=
    hT'.orthogonalFamily_eigenspaces.comp
      (f := fun μ : ℝ => (μ : ℂ)) (Complex.ofReal_injective)
  have hOrth' : OrthogonalFamily ℂ
      (fun μ : { μ : ℝ // μ ≠ 0 } => Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))
      (fun μ => (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)).subtypeₗᵢ) :=
    hOrth.comp (f := fun μ : { μ : ℝ // μ ≠ 0 } => μ.1) Subtype.val_injective
  have := hOrth'.orthonormal_sigma_orthonormal
    (v_family := fun μ : { μ : ℝ // μ ≠ 0 } =>
      haveI := finite_dimensional_eigenspace hT (μ.1 : ℂ) (by exact_mod_cast μ.2)
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)) : _ → _))
    (fun μ =>
      haveI := finite_dimensional_eigenspace hT (μ.1 : ℂ) (by exact_mod_cast μ.2)
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))).orthonormal)
  exact this

/-- Each vector of `eigenvectorFamily` really is an eigenvector of `T`, with the eigenvalue
recorded in its index. -/
theorem apply_eigenvectorFamily (hT : IsCompactOperator T) (a : EigenvectorIndex T) :
    (T : H →ₗ[ℂ] H) (eigenvectorFamily hT a) = (a.1.1 : ℂ) • eigenvectorFamily hT a := by
  apply Module.End.mem_eigenspace_iff.mp
  haveI := finite_dimensional_eigenspace hT (a.1.1 : ℂ) (by exact_mod_cast a.1.2)
  exact Submodule.coe_mem _

/-- **Only finitely many eigenvalues of a compact self-adjoint operator can exceed any fixed
positive threshold.** Key finiteness step towards countability of `EigenvectorIndex T`: if
infinitely many indices had eigenvalue `≥ ε` in absolute value, the corresponding eigenvectors
would form an orthonormal sequence whose images under `T` stay pairwise at distance `≥ ε√2`,
contradicting compactness of `T` (which forces a norm-convergent, hence Cauchy, subsequence). -/
theorem finite_large_eigenvalue_index (hT : IsCompactOperator T) (hT' : T.IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    {a : EigenvectorIndex T | ε ≤ |a.1.1|}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  classical
  set f : ℕ ↪ {a : EigenvectorIndex T | ε ≤ |a.1.1|} := hinf.natEmbedding _ with hf_def
  set e : ℕ → H := fun n => eigenvectorFamily hT (f n).1 with he_def
  have hf_inj : Function.Injective (fun n => (f n).1) := fun _ _ h => f.injective (Subtype.ext h)
  have he_orth : Orthonormal ℂ e :=
    (orthonormal_eigenvectorFamily hT hT').comp (fun n => (f n).1) hf_inj
  have hTe : ∀ n, (T : H →ₗ[ℂ] H) (e n) = ((f n).1.1.1 : ℂ) • e n :=
    fun n => apply_eigenvectorFamily hT (f n).1
  have hsep : ∀ m n, m ≠ n → Real.sqrt 2 * ε ≤ ‖T (e m) - T (e n)‖ := by
    intro m n hmn
    have hinner : inner ℂ (e m) (e n) = (0 : ℂ) := he_orth.2 hmn
    have hTinner : inner ℂ (T (e m)) (T (e n)) = (0 : ℂ) := by
      show inner ℂ ((T : H →ₗ[ℂ] H) (e m)) ((T : H →ₗ[ℂ] H) (e n)) = (0 : ℂ)
      rw [hTe m, hTe n, inner_smul_left, inner_smul_right, hinner]; simp
    have hnormsq : ‖T (e m) - T (e n)‖ ^ 2 = ‖T (e m)‖ ^ 2 + ‖T (e n)‖ ^ 2 := by
      have h0 : (inner ℂ (T (e m)) (T (e n)) : ℂ) = 0 := hTinner
      rw [@norm_sub_sq ℂ]
      have : RCLike.re (inner ℂ (T (e m)) (T (e n)) : ℂ) = 0 := by rw [h0]; simp
      rw [this]; ring
    have hTe_norm : ∀ k, ‖T (e k)‖ = |(f k).1.1.1| := by
      intro k
      show ‖(T : H →ₗ[ℂ] H) (e k)‖ = _
      rw [hTe k, norm_smul, he_orth.1 k]
      simp
    have hm_bound : ε ≤ ‖T (e m)‖ := by rw [hTe_norm]; exact (f m).2
    have hn_bound : ε ≤ ‖T (e n)‖ := by rw [hTe_norm]; exact (f n).2
    have hsq : 2 * ε ^ 2 ≤ ‖T (e m) - T (e n)‖ ^ 2 := by
      rw [hnormsq]; nlinarith [sq_nonneg (‖T (e m)‖ - ε), sq_nonneg (‖T (e n)‖ - ε)]
    have h2 : Real.sqrt (2 * ε ^ 2) ≤ ‖T (e m) - T (e n)‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (T (e m) - T (e n)))]
      exact Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (by norm_num) (ε ^ 2), Real.sqrt_sq hε.le] at h2
  obtain ⟨K, hK, hKsub⟩ := hT.image_closedBall_subset_compact 1
  have hmem : ∀ n, T (e n) ∈ K := fun n =>
    hKsub ⟨e n, by simpa using (he_orth.1 n).le, rfl⟩
  obtain ⟨y, -, φ, hφmono, hφtendsto⟩ := hK.tendsto_subseq hmem
  have hcauchy : CauchySeq (fun n => T (e (φ n))) := hφtendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (Real.sqrt 2 * ε) (by positivity)
  have hφinj : Function.Injective φ := hφmono.injective
  have := hN (N + 1) (by omega) N (by omega)
  rw [dist_eq_norm] at this
  have hge := hsep (φ (N + 1)) (φ N) (hφinj.ne (by omega))
  linarith

/-- **The eigenvector index of a compact self-adjoint operator is countable.** `EigenvectorIndex
T` is the union, over `n : ℕ`, of the (finite, by `finite_large_eigenvalue_index`) set of
indices with eigenvalue `≥ 1/(n+1)` in absolute value — every nonzero eigenvalue exceeds some
such threshold, by the Archimedean property. -/
theorem countable_eigenvectorIndex (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    Countable (EigenvectorIndex T) := by
  have hcov : (Set.univ : Set (EigenvectorIndex T)) =
      ⋃ n : ℕ, {a : EigenvectorIndex T | 1 / (n + 1 : ℝ) ≤ |a.1.1|} := by
    ext a
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr a.1.2)
    exact ⟨n, hn.le⟩
  have hfin : ∀ n : ℕ, {a : EigenvectorIndex T | 1 / (n + 1 : ℝ) ≤ |a.1.1|}.Finite :=
    fun n => finite_large_eigenvalue_index hT hT' (by positivity)
  rw [← Set.countable_univ_iff, hcov]
  exact Set.countable_iUnion fun n => (hfin n).countable

end ContinuousLinearMap
