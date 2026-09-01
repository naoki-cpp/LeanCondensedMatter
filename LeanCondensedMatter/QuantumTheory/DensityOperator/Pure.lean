import LeanCondensedMatter.QuantumTheory.DensityOperator.Basic

/-!
# Pure density states

Constructs the rank-one density operator associated with a normalized state vector.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A unit rank-one projector has no nonzero eigenvalue other than one. -/
theorem eigenspace_rankOne_eq_bot {ψ : H} (hψ : ‖ψ‖ = 1) {μ : ℂ}
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
    Module.End.eigenspace ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply] at hv
  have h1 : (inner ℂ ψ v : ℂ) = μ * (inner ℂ ψ v : ℂ) := by
    have hcast := congrArg (fun w => (inner ℂ ψ w : ℂ)) hv
    simpa [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ] using hcast
  have h1' : (inner ℂ ψ v : ℂ) * (1 - μ) = 0 := by
    rw [mul_sub, mul_one, sub_eq_zero, mul_comm]
    exact h1
  have h2 : (inner ℂ ψ v : ℂ) = 0 :=
    (mul_eq_zero.mp h1').resolve_right (sub_ne_zero.mpr hμ1.symm)
  rw [h2, zero_smul] at hv
  exact (smul_eq_zero.mp hv.symm).resolve_left hμ0

omit [CompleteSpace H] in
/-- The eigenspace at eigenvalue one of a unit rank-one projector is `span {ψ}`. -/
theorem eigenspace_rankOne_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    Module.End.eigenspace ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) 1 =
      Submodule.span ℂ {ψ} := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, one_smul] at hv
    exact Submodule.mem_span_singleton.mpr ⟨inner ℂ ψ v, hv⟩
  · rw [Submodule.span_singleton_le_iff_mem, Module.End.mem_eigenspace_iff]
    simp [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hψ]

omit [CompleteSpace H] in
/-- The eigenspace at eigenvalue one of a unit rank-one projector has dimension one. -/
theorem finrank_eigenspace_rankOne_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    Module.finrank ℂ (Module.End.eigenspace
      ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (1 : ℂ)) = 1 := by
  rw [eigenspace_rankOne_one hψ]
  exact finrank_span_singleton (by rw [ne_eq, ← norm_eq_zero, hψ]; norm_num)

/-- The eigenvector index of a unit rank-one projector has a unique element. -/
@[reducible] def uniqueEigenvectorIndexRankOne {ψ : H} (hψ : ‖ψ‖ = 1) :
    Unique (EigenvectorIndex (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) where
  default := ⟨⟨1, one_ne_zero⟩, ⟨0, by
    change 0 < Module.finrank ℂ (Module.End.eigenspace
      ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (1 : ℂ))
    rw [finrank_eigenspace_rankOne_one hψ]
    norm_num⟩⟩
  uniq := by
    rintro ⟨⟨μ, hμ0⟩, i⟩
    have hμ1 : μ = 1 := by
      by_contra hne
      have hbot := eigenspace_rankOne_eq_bot (ψ := ψ) hψ (μ := (μ : ℂ))
        (by exact_mod_cast hμ0) (by exact_mod_cast hne)
      have hfr : Module.finrank ℂ (Module.End.eigenspace
          ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ : ℂ)) = 0 := by
        rw [hbot]
        exact finrank_bot ℂ H
      exact (Nat.not_lt_zero i.1) (hfr ▸ i.isLt)
    subst hμ1
    change (⟨⟨(1 : ℝ), hμ0⟩, i⟩ : EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) = _
    congr 1
    refine Fin.ext ?_
    have hfr : Module.finrank ℂ (Module.End.eigenspace
        ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H)
        (((⟨(1 : ℝ), hμ0⟩ : {γ : ℝ // γ ≠ 0}).1 : ℝ) : ℂ)) = 1 :=
      finrank_eigenspace_rankOne_one hψ
    have hilt := i.isLt
    omega

omit [CompleteSpace H] in
/-- The nonzero real eigenvalues of a unit rank-one projector are summable. -/
theorem rankOne_hasSummableRealEigenvalues {ψ : H} (hψ : ‖ψ‖ = 1) :
    HasSummableRealEigenvalues (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  exact Summable.of_finite

omit [CompleteSpace H] in
/-- A unit rank-one projector has spectral trace one. -/
theorem rankOne_spectralTrace_eq_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    spectralTrace (InnerProductSpace.rankOne ℂ ψ ψ) = 1 := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  change (∑' a : EigenvectorIndex
    (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H), a.1.1) = 1
  rw [tsum_eq_single (uniqueEigenvectorIndexRankOne hψ).default (fun b hb =>
    absurd (Subsingleton.elim b (uniqueEigenvectorIndexRankOne hψ).default) hb)]
  rfl

/-- A normalized pure state defines its rank-one density operator. -/
noncomputable def pure (ψ : State H) : DensityOperator H := by
  let htraceClass : SpectralTraceClass
      (InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) :=
    SpectralTraceClass.ofPositive
      (ContinuousLinearMap.isCompactOperator_rankOne ψ.1 ψ.1)
      (InnerProductSpace.isPositive_rankOne_self ψ.1)
      (rankOne_hasSummableRealEigenvalues ψ.2)
  exact {
    op := InnerProductSpace.rankOne ℂ ψ.1 ψ.1
    pos := InnerProductSpace.isPositive_rankOne_self ψ.1
    spectralTraceClass := htraceClass
    spectralTrace_eq_one := by
      rw [htraceClass.trace_eq_spectralTrace]
      exact rankOne_spectralTrace_eq_one ψ.2 }

end QuantumTheory
