import LeanCondensedMatter.Analysis.CompactSelfAdjoint
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Axiomatic quantum theory: density operators via trace-class operators (infinite dimensions)

Extends the density-operator postulate (`QuantumTheory.DensityOperator` in
`QuantumTheory/DensityOperator.lean`) beyond finite-dimensional `H`, using the general
`ContinuousLinearMap.trace` for compact self-adjoint trace-class operators
(`LeanCondensedMatter/Analysis/CompactSelfAdjoint.lean`) in place of `LinearMap.trace`, which
requires finite-dimensionality.

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.DensityOperator`
and everything built on it (`POVM`, `prob`, `sum_prob_eq_one`, `purity`, ...) are untouched. This
namespace develops the infinite-dimensional analogue in parallel.

**Scope note (a genuine mathematical gap, not just a Lean technicality):** in finite dimensions
`LinearMap.trace` is defined unconditionally, so `Tr[E_m ρ]` (the Born-rule probability, needed
for `prob`/`sum_prob_eq_one`) makes sense for *any* positive `E_m` and density operator `ρ`. In
this infinite-dimensional setting, `ContinuousLinearMap.trace` is only meaningful for *compact
self-adjoint trace-class* operators — and `E_m ∘ ρ` need not be self-adjoint at all (a product of
two self-adjoint operators is self-adjoint only when they commute). Porting `prob`/`sum_prob_eq_one`
therefore needs a notion of trace for non-self-adjoint (e.g. Hilbert–Schmidt-class) operators that
does not yet exist in this project; see `notes/roadmaps/operator-algebra.md`. This file is
deliberately scoped to what's well-posed without that: the `DensityOperator` structure itself and
properties of a single density operator (`pure`, and eventually `purity`, which only needs `ρ ∘ ρ`
— self-adjoint since `ρ` is).
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Density operator postulate (infinite-dimensional).** A positive, compact, trace-class
operator of trace `1`. The compactness and trace-class hypotheses are carried explicitly (rather
than derived from positivity/boundedness alone, which is not in general enough) — matching the
style of `ContinuousLinearMap.trace_add`/`trace_comp_comm`, which also take these as explicit
hypotheses. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  op : H →L[ℂ] H
  pos : op.IsPositive
  compact : IsCompactOperator op
  traceClass : op.IsTraceClass
  trace_eq_one : trace traceClass = 1

/-- A density operator's underlying operator is self-adjoint (in the `IsSymmetric` sense used
throughout `Analysis/CompactSelfAdjoint.lean`), inherited from positivity. -/
theorem DensityOperator.isSymmetric (ρ : DensityOperator H) : (ρ.op : H →ₗ[ℂ] H).IsSymmetric :=
  ρ.pos.isSelfAdjoint.isSymmetric

/-- **A rank-one operator `|x⟩⟨y|` is a compact operator**, regardless of the (possibly
infinite) dimension of `H`: it factors as the composition of the (automatically compact, since
its codomain `ℂ` is locally compact) functional `y ↦ ⟪y, ·⟫` with the continuous linear map
`c ↦ c • x`, and `IsCompactOperator` is preserved under post-composition by a continuous linear
map. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y : H →L[ℂ] H) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- The rank-one projector `|ψ⟩⟨ψ|` for a unit vector `ψ` has no eigenvectors outside its own
eigenspace at `1`: any other nonzero eigenvalue's eigenspace is trivial. -/
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
    rw [mul_sub, mul_one, sub_eq_zero, mul_comm]; exact h1
  have h2 : (inner ℂ ψ v : ℂ) = 0 :=
    (mul_eq_zero.mp h1').resolve_right (sub_ne_zero.mpr hμ1.symm)
  rw [h2, zero_smul] at hv
  exact (smul_eq_zero.mp hv.symm).resolve_left hμ0

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

/-- The rank-one projector `|ψ⟩⟨ψ|`'s eigenspace at eigenvalue `1` has dimension `1`. -/
theorem finrank_eigenspace_rankOne_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    Module.finrank ℂ (Module.End.eigenspace
      ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (1 : ℂ)) = 1 := by
  rw [eigenspace_rankOne_one hψ]
  exact finrank_span_singleton (by rw [ne_eq, ← norm_eq_zero, hψ]; norm_num)

/-- **The eigenvector index of a rank-one projector `|ψ⟩⟨ψ|` (unit `ψ`) has a unique element**,
the single eigenvector `ψ` itself at eigenvalue `1`: every other nonzero eigenvalue's eigenspace
is trivial (`eigenspace_rankOne_eq_bot`), forcing its `Fin`-indexed fiber to be empty. -/
def uniqueEigenvectorIndexRankOne {ψ : H} (hψ : ‖ψ‖ = 1) :
    Unique (ContinuousLinearMap.EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) where
  default := ⟨⟨1, one_ne_zero⟩, ⟨0, by
    show 0 < Module.finrank ℂ (Module.End.eigenspace
      ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (1 : ℂ))
    rw [finrank_eigenspace_rankOne_one hψ]; norm_num⟩⟩
  uniq := by
    rintro ⟨⟨μ, hμ0⟩, i⟩
    have hμ1 : μ = 1 := by
      by_contra hne
      have hbot := eigenspace_rankOne_eq_bot (ψ := ψ) hψ (μ := (μ : ℂ))
        (by exact_mod_cast hμ0) (by exact_mod_cast hne)
      have hfr : Module.finrank ℂ (Module.End.eigenspace
          ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ : ℂ)) = 0 := by
        rw [hbot]; exact finrank_bot ℂ H
      exact (Nat.not_lt_zero i.1) (hfr ▸ i.isLt)
    subst hμ1
    show (⟨⟨(1 : ℝ), hμ0⟩, i⟩ : ContinuousLinearMap.EigenvectorIndex
      (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H)) = _
    congr 1
    refine Fin.ext ?_
    have hfr : Module.finrank ℂ (Module.End.eigenspace
        ((InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) : H →ₗ[ℂ] H)
        (((⟨(1 : ℝ), hμ0⟩ : { γ : ℝ // γ ≠ 0 }).1 : ℝ) : ℂ)) = 1 :=
      finrank_eigenspace_rankOne_one hψ
    have hilt := i.isLt
    omega

/-- **`pure ψ` is trace-class, with trace `1`.** -/
theorem rankOne_isTraceClass {ψ : H} (hψ : ‖ψ‖ = 1) :
    ContinuousLinearMap.IsTraceClass (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H) := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  exact Summable.of_finite

theorem rankOne_trace_eq_one {ψ : H} (hψ : ‖ψ‖ = 1) :
    ContinuousLinearMap.trace (rankOne_isTraceClass hψ) = 1 := by
  haveI := uniqueEigenvectorIndexRankOne hψ
  show (∑' a : ContinuousLinearMap.EigenvectorIndex
    (InnerProductSpace.rankOne ℂ ψ ψ : H →L[ℂ] H), a.1.1) = 1
  rw [tsum_eq_single (uniqueEigenvectorIndexRankOne hψ).default (fun b hb =>
    absurd (Subsingleton.elim b (uniqueEigenvectorIndexRankOne hψ).default) hb)]
  rfl

/-- **Purification (infinite-dimensional).** A pure state `ψ` gives rise to a density operator,
the rank-one projector `|ψ⟩⟨ψ|`. -/
noncomputable def pure (ψ : QuantumTheory.State H) : DensityOperator H where
  op := InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  pos := InnerProductSpace.isPositive_rankOne_self ψ.1
  compact := isCompactOperator_rankOne ψ.1 ψ.1
  traceClass := rankOne_isTraceClass ψ.2
  trace_eq_one := rankOne_trace_eq_one ψ.2

end QuantumTheory.TraceClass
