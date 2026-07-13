import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive

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

/-- The (algebraic) span of `eigenvectorFamily` is exactly the sum of all the nonzero
eigenspaces: each per-eigenspace `stdOrthonormalBasis` spans its own (finite-dimensional)
eigenspace, and these are glued together in the same way as the index type. -/
theorem span_eigenvectorFamily (hT : IsCompactOperator T) :
    Submodule.span ℂ (Set.range (eigenvectorFamily hT)) =
      ⨆ μ : { μ : ℝ // μ ≠ 0 }, Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨a, rfl⟩
    exact Submodule.mem_iSup_of_mem a.1 (by
      haveI := finite_dimensional_eigenspace hT (a.1.1 : ℂ) (by exact_mod_cast a.1.2)
      exact Submodule.coe_mem _)
  · apply iSup_le
    intro μ
    haveI := finite_dimensional_eigenspace hT (μ.1 : ℂ) (by exact_mod_cast μ.2)
    have hbasis : Submodule.span ℂ
        (Set.range (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)))) =
        (⊤ : Submodule ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))) :=
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))).toBasis.span_eq
    have hmap : Submodule.map (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ)).subtype
        (Submodule.span ℂ
          (Set.range (stdOrthonormalBasis ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ))))) =
        Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ.1 : ℂ) := by
      rw [hbasis, Submodule.map_top, Submodule.range_subtype]
    rw [← hmap, Submodule.map_span]
    apply Submodule.span_mono
    rintro x ⟨v, ⟨y, rfl⟩, rfl⟩
    exact ⟨⟨μ, y⟩, rfl⟩

/-- **The closure of the nonzero-eigenspace part and the kernel are exactly each other's
orthogonal complements.** The key structural fact enabling the `tsum` reconstruction of `T`:
`ker T` and `eigenvectorFamily`'s span are mutually orthogonal (distinct eigenspaces), and
their algebraic sum is dense — it equals the sum of *all* eigenspaces, dense by
`orthogonalComplement_iSup_eigenspaces_eq_bot`, since a self-adjoint operator's eigenvalues are
always real (so no eigenspace outside `ℝ` contributes). -/
theorem orthogonal_closure_span_eigenvectorFamily (hT : IsCompactOperator T)
    (hT' : T.IsSymmetric) :
    (Submodule.span ℂ (Set.range (eigenvectorFamily hT))).topologicalClosureᗮ =
      Module.End.eigenspace (T : H →ₗ[ℂ] H) (0 : ℂ) := by
  set E' := Submodule.span ℂ (Set.range (eigenvectorFamily hT)) with hE'_def
  set F := E'.topologicalClosure with hF_def
  set G := Module.End.eigenspace (T : H →ₗ[ℂ] H) (0 : ℂ) with hG_def
  have hOrth : OrthogonalFamily ℂ (fun μ : ℝ => Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ))
      (fun μ => (Module.End.eigenspace (T : H →ₗ[ℂ] H) (μ : ℂ)).subtypeₗᵢ) :=
    hT'.orthogonalFamily_eigenspaces.comp (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective
  -- `E' ⊆ Gᗮ`
  have hE'G : E' ≤ Gᗮ := by
    rw [hE'_def, Submodule.span_le]
    rintro x ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal']
    intro u hu
    haveI := finite_dimensional_eigenspace hT (a.1.1 : ℂ) (by exact_mod_cast a.1.2)
    have hxmem : eigenvectorFamily hT a ∈ Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ) :=
      Submodule.coe_mem _
    have hne : a.1.1 ≠ (0 : ℝ) := a.1.2
    have := hOrth hne (⟨eigenvectorFamily hT a, hxmem⟩ :
        Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ)) (⟨u, hu⟩ : G)
    simpa using this
  -- `G` is closed (it's the kernel of the continuous map `T`), hence complete.
  have hGclosed : IsClosed (G : Set H) := by
    have heq : G = LinearMap.ker (T : H →ₗ[ℂ] H) := by
      ext x
      rw [hG_def, Module.End.mem_eigenspace_iff, LinearMap.mem_ker, zero_smul]
    rw [heq]; exact T.isClosed_ker
  haveI : CompleteSpace G := hGclosed.completeSpace_coe
  -- `F ⊆ Gᗮ`, hence `G ⊆ Fᗮ`.
  have hFG : F ≤ Gᗮ := hF_def ▸ E'.topologicalClosure_minimal hE'G G.isClosed_orthogonal
  have hGF : G ≤ Fᗮ := Submodule.le_orthogonal_iff_le_orthogonal.mpr hFG
  -- Density: `G ⊔ E'` equals the sum of *all* eigenspaces (over `ℂ`), which is dense.
  have hsup : (⨆ μ : ℂ, Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) = G ⊔ E' := by
    apply le_antisymm
    · apply iSup_le
      intro μ
      rcases eq_or_ne (Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) ⊥ with hbot | hne
      · rw [hbot]; exact bot_le
      · have hreal : (starRingEnd ℂ) μ = μ := hT'.conj_eigenvalue_eq_self hne
        have hre : (μ.re : ℂ) = μ := Complex.conj_eq_iff_re.mp hreal
        rcases eq_or_ne μ.re 0 with hz | hz
        · rw [← hre, hz, Complex.ofReal_zero]; exact le_sup_left
        · refine le_trans ?_ le_sup_right
          rw [← hre, hE'_def, span_eigenvectorFamily hT]
          exact le_iSup (fun ν : { ν : ℝ // ν ≠ 0 } =>
            Module.End.eigenspace (T : H →ₗ[ℂ] H) (ν.1 : ℂ)) ⟨μ.re, hz⟩
    · refine sup_le (le_iSup (fun μ : ℂ => Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) 0) ?_
      rw [hE'_def, span_eigenvectorFamily hT]
      exact iSup_le fun ν => le_iSup
        (fun μ : ℂ => Module.End.eigenspace (T : H →ₗ[ℂ] H) μ) (ν.1 : ℂ)
  have hdense : (G ⊔ E').topologicalClosure = ⊤ := by
    rw [← hsup, ← Submodule.orthogonal_orthogonal_eq_closure,
      orthogonalComplement_iSup_eigenspaces_eq_bot hT hT', Submodule.bot_orthogonal_eq_top]
  -- Combine: `G ⊆ Fᗮ`, and `G ⊔ F` is dense (since it contains `G ⊔ E'`), so `Fᗮ ⊆ G`.
  have hFGdense : (F ⊔ G).topologicalClosure = ⊤ := by
    have hle : G ⊔ E' ≤ F ⊔ G := by
      have h1 : E' ≤ F := hF_def ▸ E'.le_topologicalClosure
      calc G ⊔ E' ≤ G ⊔ F := sup_le_sup_left h1 G
        _ = F ⊔ G := sup_comm ..
    have hmono := Submodule.topologicalClosure_mono hle
    rw [hdense] at hmono
    exact top_le_iff.mp hmono
  have hFGbot : Fᗮ ⊓ Gᗮ = ⊥ := by
    rw [Submodule.inf_orthogonal, ← Submodule.orthogonal_closure, hFGdense]
    exact Submodule.top_orthogonal_eq_bot
  refine le_antisymm ?_ hGF
  intro v hv
  obtain ⟨g, hg, g', hg', rfl⟩ := G.exists_add_mem_mem_orthogonal (v := v)
  have hg'F : g' ∈ Fᗮ := by
    have : g' = (g + g') - g := by abel
    rw [this]
    exact Fᗮ.sub_mem hv (hGF hg)
  have : g' ∈ Fᗮ ⊓ Gᗮ := ⟨hg'F, hg'⟩
  rw [hFGbot, Submodule.mem_bot] at this
  rwa [this, add_zero]

/-- `eigenvectorFamily`, recast as a `HilbertBasis` of the closed subspace it spans (its span's
orthogonal complement is trivial *within that subspace*, by density of the span in its own
closure). -/
noncomputable def eigenvectorHilbertBasis (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    HilbertBasis (EigenvectorIndex T) ℂ
      (Submodule.span ℂ (Set.range (eigenvectorFamily hT))).topologicalClosure := by
  set E' := Submodule.span ℂ (Set.range (eigenvectorFamily hT)) with hE'_def
  set F := E'.topologicalClosure with hF_def
  have hmem : ∀ a, eigenvectorFamily hT a ∈ F := fun a =>
    hF_def ▸ E'.le_topologicalClosure (hE'_def ▸ Submodule.subset_span ⟨a, rfl⟩)
  refine HilbertBasis.mkOfOrthogonalEqBot
    (v := fun a => (⟨eigenvectorFamily hT a, hmem a⟩ : F)) ?_ ?_
  · constructor
    · intro a
      have := (orthonormal_eigenvectorFamily hT hT').1 a
      rwa [show ‖(⟨eigenvectorFamily hT a, hmem a⟩ : F)‖ = ‖eigenvectorFamily hT a‖ from rfl]
    · intro a b hab
      have := (orthonormal_eigenvectorFamily hT hT').2 hab
      rwa [Submodule.coe_inner]
  · rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    have hdense : Dense (Submodule.span ℂ
        (Set.range (fun a => (⟨eigenvectorFamily hT a, hmem a⟩ : F))) : Set F) := by
      rw [F.subtypeₗᵢ.isometry.isEmbedding.isInducing.dense_iff]
      intro y
      have hspaneq : Submodule.map F.subtypeₗᵢ.toLinearMap
          (Submodule.span ℂ (Set.range (fun a => (⟨eigenvectorFamily hT a, hmem a⟩ : F)))) =
          E' := by
        rw [Submodule.map_span, hE'_def]
        congr 1
        ext z
        constructor
        · rintro ⟨-, ⟨a, rfl⟩, rfl⟩; exact ⟨a, rfl⟩
        · rintro ⟨a, rfl⟩; exact ⟨_, ⟨a, rfl⟩, rfl⟩
      have himg : F.subtypeₗᵢ '' (Submodule.span ℂ
          (Set.range (fun a => (⟨eigenvectorFamily hT a, hmem a⟩ : F))) : Set F) =
          (E' : Set H) := by
        rw [← hspaneq]
        exact (Submodule.map_coe _ _).symm
      rw [himg, ← Submodule.topologicalClosure_coe, ← hF_def]
      exact y.2
    have hclosed : IsClosed {y : F | inner ℂ x y = (0 : ℂ)} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : (Submodule.span ℂ
        (Set.range (fun a => (⟨eigenvectorFamily hT a, hmem a⟩ : F))) : Set F) ⊆
        {y : F | inner ℂ x y = (0 : ℂ)} := hx
    have hall : ∀ y : F, inner ℂ x y = (0 : ℂ) := fun y =>
      (hclosed.closure_subset_iff.mpr hsub) (hdense y)
    have := hall x
    rwa [inner_self_eq_zero] at this

/-- **The `tsum` reconstruction of a compact self-adjoint operator from its eigenvectors.** For
any `x : H`, `T x` is the sum, over `EigenvectorIndex T`, of `T`'s eigenvector expansion of `x`:
`T x = ∑' a, (eigenvalue a : ℂ) • ⟪eigenvectorFamily a, x⟫ • eigenvectorFamily a`. This is
Track C's step 1 goal (`notes/roadmaps/operator-algebra.md`), the infinite-dimensional analogue
of the finite-dimensional eigenbasis expansions used throughout `QuantumTheory/Entropy.lean`. -/
theorem hasSum_eigenvectorFamily (hT : IsCompactOperator T) (hT' : T.IsSymmetric) (x : H) :
    HasSum (fun a : EigenvectorIndex T =>
      (a.1.1 : ℂ) • (inner ℂ (eigenvectorFamily hT a) x : ℂ) • eigenvectorFamily hT a) (T x) := by
  set E' := Submodule.span ℂ (Set.range (eigenvectorFamily hT)) with hE'_def
  set F := E'.topologicalClosure with hF_def
  set G := Module.End.eigenspace (T : H →ₗ[ℂ] H) (0 : ℂ) with hG_def
  set b := eigenvectorHilbertBasis hT hT'
  have hb : ∀ a, (b a : H) = eigenvectorFamily hT a := fun a => by
    simp [b, eigenvectorHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hstep1 : HasSum (fun a : EigenvectorIndex T => (inner ℂ (b a : H) x : ℂ) • (b a : H))
      (F.subtypeₗᵢ (F.orthogonalProjectionOnto x)) :=
    (b.hasSum_orthogonalProjectionOnto x).mapL F.subtypeₗᵢ.toContinuousLinearMap
  have hstarProj : F.subtypeₗᵢ (F.orthogonalProjectionOnto x) = F.starProjection x := rfl
  rw [hstarProj] at hstep1
  have hTproj : T (F.starProjection x) = T x := by
    have hmem : x - F.starProjection x ∈ Fᗮ := F.sub_starProjection_mem_orthogonal x
    have hFG : Fᗮ = G := orthogonal_closure_span_eigenvectorFamily hT hT'
    rw [hFG] at hmem
    have : (T : H →ₗ[ℂ] H) (x - F.starProjection x) = 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul] at hmem; exact hmem
    have hTlin : (T : H →ₗ[ℂ] H) x - (T : H →ₗ[ℂ] H) (F.starProjection x) = 0 := by
      rw [← map_sub]; exact this
    have := sub_eq_zero.mp hTlin
    exact this.symm
  have hstep2 := hstep1.mapL T
  rw [hTproj] at hstep2
  have heq : ∀ a, T ((inner ℂ (b a : H) x : ℂ) • (b a : H)) =
      (a.1.1 : ℂ) • (inner ℂ (eigenvectorFamily hT a) x : ℂ) • eigenvectorFamily hT a := by
    intro a
    rw [ContinuousLinearMap.map_smul, hb a]
    show (inner ℂ (eigenvectorFamily hT a) x : ℂ) • (T : H →ₗ[ℂ] H) (eigenvectorFamily hT a) = _
    rw [apply_eigenvectorFamily hT a, smul_smul, smul_smul, mul_comm]
  simpa only [heq] using hstep2

/-- **A compact self-adjoint operator is trace-class** when the absolute values of its
(nonzero) eigenvalues, with multiplicity, are summable. This is Track C's step 2
(`notes/roadmaps/operator-algebra.md`) — the finite-dimensional analogue is automatic (a
finite sum is always summable), so this predicate is the substantive content that's new in
infinite dimensions.

No separate "independent of the choice of eigenbasis" lemma is needed here: `EigenvectorIndex
T` and the eigenvalue recorded at each index (`a.1.1`) depend only on the eigenspaces of `T`
themselves and their dimensions, not on which orthonormal basis `stdOrthonormalBasis` happens
to pick within each (possibly multi-dimensional) eigenspace — every basis vector of a given
eigenspace shares the same eigenvalue, so `Summable (fun a => |a.1.1|)` is manifestly
insensitive to that choice. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  Summable (fun a : EigenvectorIndex T => |a.1.1|)

/-- **The trace of a trace-class compact self-adjoint operator**: the sum of its (nonzero)
eigenvalues, with multiplicity. This is Track C's step 4 (`notes/roadmaps/operator-algebra.md`),
the infinite-dimensional analogue of `LinearMap.trace` used throughout
`QuantumTheory/Entropy.lean` in the finite-dimensional case. -/
noncomputable def trace {T : H →L[ℂ] H} (_h : IsTraceClass T) : ℝ :=
  ∑' a : EigenvectorIndex T, a.1.1

/-- The trace of a positive trace-class operator is nonnegative — as for a density operator's
`LinearMap.trace` in the finite-dimensional case (`QuantumTheory.DensityOperator`), every
eigenvalue of a positive operator is nonnegative. -/
theorem trace_nonneg {T : H →L[ℂ] H} (h : IsTraceClass T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) : 0 ≤ trace h := by
  refine tsum_nonneg fun a => ?_
  have hpos_finrank : 0 < Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) a.2.isLt
  have hne : Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot ℂ H] at hpos_finrank
    exact absurd hpos_finrank (lt_irrefl 0)
  exact eigenvalue_nonneg_of_nonneg hne hpos.re_inner_nonneg_right

end ContinuousLinearMap
