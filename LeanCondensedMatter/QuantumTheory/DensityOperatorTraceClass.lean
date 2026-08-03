import LeanCondensedMatter.Analysis.Operator.TraceClass.Bundled
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Axiomatic quantum theory: density operators via spectral trace (infinite dimensions)

Extends the density-operator postulate (`QuantumTheory.DensityOperator` in
`QuantumTheory/DensityOperator.lean`) beyond finite-dimensional `H`. The infinite-dimensional
operator carries one canonical `ContinuousLinearMap.SpectralTraceClass` bundle rather than
separate compactness and spectral-summability fields plus a later compatibility bridge.

The trace-class namespace also contains the canonical discrete `POVM` data type. Its outcome type
may be any countable type, and normalization is expressed by strong pointwise summation. The Born
probability API is defined downstream in `QuantumTheory/POVMTraceClass.lean`, after the normalized
complex expectation functional is available.

The finite-dimensional `QuantumTheory.DensityOperator` and `QuantumTheory.POVM` remain separate
because they use the finite-dimensional state representation rather than the trace-class state.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Density operator postulate (infinite-dimensional).** A positive operator carrying bundled
compactness, symmetry, and summability of its nonzero real eigenvalues, with spectral trace `1`. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →L[ℂ] H
  pos : op.IsPositive
  spectralTraceClass : SpectralTraceClass op
  spectralTrace_eq_one : spectralTraceClass.trace = 1

/-- A density operator's underlying operator is self-adjoint. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.spectralTraceClass.symmetric

/-- The diagonal matrix elements of a density operator sum to `1` against any Hilbert basis. -/
theorem DensityOperator.hasSum_inner_apply_eq_one (ρ : DensityOperator H)
    {ι : Type*} (d : HilbertBasis ι ℂ H) :
    HasSum (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) 1 := by
  have h := ρ.spectralTraceClass.hasSum_inner_apply d
  rwa [ρ.spectralTrace_eq_one] at h

/-- The diagonal sum over any orthonormal family is bounded above by `1`. -/
theorem DensityOperator.sum_inner_apply_le_one (ρ : DensityOperator H)
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d) :
    Summable (fun i => (inner ℂ (d i) (ρ.op (d i)) : ℂ).re) ∧
      ∑' i, (inner ℂ (d i) (ρ.op (d i)) : ℂ).re ≤ 1 := by
  have h := ρ.spectralTraceClass.sum_inner_apply_le_trace ρ.pos.toLinearMap hd
  rwa [ρ.spectralTrace_eq_one] at h

omit [CompleteSpace H] in
/-- **A rank-one operator `|x⟩⟨y|` is compact**, regardless of the dimension of `H`. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y : H →L[ℂ] H) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

omit [CompleteSpace H] in
/-- The rank-one projector `|ψ⟩⟨ψ|` for a unit vector `ψ` has no eigenvectors outside its own
eigenspace at `1`. -/
theorem eigenspace_rankOne_eq_bot {ψ : H} (hψ : ‖ψ‖ = 1) {μ : ℂ} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1) :
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
/-- The rank-one projector `|ψ⟩⟨ψ|` for a unit vector `ψ` has eigenspace `span {ψ}` at
 eigenvalue `1`. -/
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
/-- The rank-one projector's eigenspace at eigenvalue `1` has dimension `1`. -/
theorem finrank_eigenspace_rankOne_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    Module.finrank ℂ (Module.End.eigenspace
      ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (1 : ℂ)) = 1 := by
  rw [eigenspace_rankOne_one hψ]
  exact finrank_span_singleton (by rw [ne_eq, ← norm_eq_zero, hψ]; norm_num)

/-- The eigenvector index of a unit rank-one projector has a unique element. -/
@[reducible] def uniqueEigenvectorIndexRankOne {ψ : H} (hψ : ‖ψ‖ = 1) :
    Unique (ContinuousLinearMap.EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) where
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
    change (⟨⟨(1 : ℝ), hμ0⟩, i⟩ : ContinuousLinearMap.EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) = _
    congr 1
    refine Fin.ext ?_
    have hfr : Module.finrank ℂ (Module.End.eigenspace
        ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H)
        (((⟨(1 : ℝ), hμ0⟩ : { γ : ℝ // γ ≠ 0 }).1 : ℝ) : ℂ)) = 1 :=
      finrank_eigenspace_rankOne_one hψ
    have hilt := i.isLt
    omega

omit [CompleteSpace H] in
/-- The nonzero real eigenvalues of a unit rank-one projector are summable. -/
theorem rankOne_hasSummableRealEigenvalues {ψ : H} (hψ : ‖ψ‖ = 1) :
    ContinuousLinearMap.HasSummableRealEigenvalues
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  exact Summable.of_finite

omit [CompleteSpace H] in
/-- A unit rank-one projector has spectral trace `1`. -/
theorem rankOne_spectralTrace_eq_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    ContinuousLinearMap.spectralTrace (rankOne_hasSummableRealEigenvalues hψ) = 1 := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  change (∑' a : ContinuousLinearMap.EigenvectorIndex
    (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H), a.1.1) = 1
  rw [tsum_eq_single (uniqueEigenvectorIndexRankOne hψ).default (fun b hb =>
    absurd (Subsingleton.elim b (uniqueEigenvectorIndexRankOne hψ).default) hb)]
  rfl

/-- **Pure-state density-operator embedding (infinite-dimensional).** -/
noncomputable def pure (ψ : QuantumTheory.State H) : DensityOperator H where
  op := InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  pos := InnerProductSpace.isPositive_rankOne_self ψ.1
  spectralTraceClass := SpectralTraceClass.ofPositive
    (isCompactOperator_rankOne ψ.1 ψ.1)
    (InnerProductSpace.isPositive_rankOne_self ψ.1)
    (rankOne_hasSummableRealEigenvalues ψ.2)
  spectralTrace_eq_one := rankOne_spectralTrace_eq_one ψ.2

/-- Each vector of `ρ`'s eigenvector family is a unit vector. -/
theorem eigenvectorFamily_norm_eq_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) :
    ‖eigenvectorFamily ρ.spectralTraceClass.compact a‖ = 1 :=
  (orthonormal_eigenvectorFamily ρ.spectralTraceClass.compact ρ.isSymmetric).1 a

/-- A discrete POVM with countably many positive bounded effects summing strongly to the identity. -/
structure POVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : Type*) [Countable M] where
  E : M → H →L[ℂ] H
  pos : ∀ m, (E m).IsPositive
  hasSum_apply : ∀ x, HasSum (fun m => E m x) x

end QuantumTheory.TraceClass
