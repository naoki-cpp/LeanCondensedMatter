import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# Spectral summability and trace for compact self-adjoint operators

Defines the precise spectral predicate `HasSummableRealEigenvalues` and its associated
`spectralTrace` on top of `EigenvectorFamily.lean`'s `EigenvectorIndex`. The historical names
`IsTraceClass` and `trace` remain compatibility aliases for downstream code.

These declarations are not yet a general trace-class ideal: the predicate records only absolute
summability of the indexed nonzero real eigenvalues. Compactness and symmetry remain explicit
hypotheses of the operator theorems that use the spectral expansion. See
`notes/roadmaps/operator-algebra.md` (Track C).
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

/-- The absolute values of the indexed nonzero real eigenvalues of `T`, with multiplicity, are
summable.

For the compact self-adjoint operators used by this project, this is the spectral summability
condition underlying trace-class arguments. The predicate itself deliberately does **not** assert
compactness or symmetry; those hypotheses are supplied separately wherever the spectral theorem is
used.

No separate "independent of the choice of eigenbasis" lemma is needed here: `EigenvectorIndex T`
and the eigenvalue recorded at each index (`a.1.1`) depend only on the eigenspaces of `T` and their
dimensions, not on which orthonormal basis `stdOrthonormalBasis` happens to pick within each
(possibly multi-dimensional) eigenspace. -/
def HasSummableRealEigenvalues (T : H →L[ℂ] H) : Prop :=
  Summable (fun a : EigenvectorIndex T => |a.1.1|)

/-- Compatibility name for the project's existing compact-self-adjoint spectral trace API.

This alias is not a claim that the project currently defines the general operator-ideal notion of
trace class. New infrastructure should prefer `HasSummableRealEigenvalues` when referring only to
the predicate defined in this file. -/
abbrev IsTraceClass (T : H →L[ℂ] H) : Prop :=
  HasSummableRealEigenvalues T

/-- The spectral sum of the indexed nonzero real eigenvalues of `T`, with multiplicity. For a
compact self-adjoint operator satisfying `HasSummableRealEigenvalues`, this is the project's
infinite-dimensional trace. -/
noncomputable def spectralTrace {T : H →L[ℂ] H} (_h : HasSummableRealEigenvalues T) : ℝ :=
  ∑' a : EigenvectorIndex T, a.1.1

/-- Compatibility name for `spectralTrace`. -/
noncomputable abbrev trace {T : H →L[ℂ] H} (h : IsTraceClass T) : ℝ :=
  spectralTrace h

omit [CompleteSpace H] in
/-- **Every eigenvalue of a positive operator is nonnegative** — the per-index fact underlying
both `trace_nonneg` below and `QuantumTheory.TraceClass.eigenvalue_nonneg` (a density operator's
eigenvalues are probabilities). -/
theorem eigenvalue_nonneg_of_isPositive {T : H →L[ℂ] H} (hpos : (T : H →ₗ[ℂ] H).IsPositive)
    (a : EigenvectorIndex T) : 0 ≤ a.1.1 := by
  have hpos_finrank : 0 < Module.finrank ℂ (Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ)) :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) a.2.isLt
  have hne : Module.End.eigenspace (T : H →ₗ[ℂ] H) (a.1.1 : ℂ) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot ℂ H] at hpos_finrank
    exact absurd hpos_finrank (lt_irrefl 0)
  exact eigenvalue_nonneg_of_nonneg hne hpos.re_inner_nonneg_right

omit [CompleteSpace H] in
/-- The trace of a positive trace-class operator is nonnegative — as for a density operator's
`LinearMap.trace` in the finite-dimensional case (`QuantumTheory.DensityOperator`), every
eigenvalue of a positive operator is nonnegative. -/
theorem trace_nonneg {T : H →L[ℂ] H} (h : IsTraceClass T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) : 0 ≤ trace h :=
  tsum_nonneg fun a => eigenvalue_nonneg_of_isPositive hpos a

omit [CompleteSpace H] in
theorem summable_eigenvectorIndex_of_isTraceClass {S : H →L[ℂ] H} (hS : IsTraceClass S) :
    Summable (fun a : EigenvectorIndex S => a.1.1) := by
  have hS' : Summable (fun a : EigenvectorIndex S => |a.1.1|) := hS
  exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using hS')

omit [CompleteSpace H] in
/-- Splits the trace-defining `tsum` over `EigenvectorIndex S` into an outer sum over the
(base) nonzero eigenvalues and an inner, *finite* sum over each eigenspace's basis vectors.
Since the summand `a ↦ a.1.1` only depends on the base component `a.1`, the inner sum is just
`finrank • μ.1`. Splitting this way (rather than reindexing `EigenvectorIndex` itself via a
dependent `Sigma`/`Fin.cast` equivalence) avoids the `Fin`/`HEq` casting machinery that turned out
to make even shallow `rfl` checks time out in the kernel (see `notes/caveats.md`). -/
theorem tsum_eigenvectorIndex_eq_tsum_mul_finrank {S : H →L[ℂ] H}
    (hS : Summable (fun a : EigenvectorIndex S => a.1.1)) :
    ∑' a : EigenvectorIndex S, a.1.1 =
      ∑' μ : { ν : ℝ // ν ≠ 0 },
        (Module.finrank ℂ (Module.End.eigenspace (S : H →ₗ[ℂ] H) (μ.1 : ℂ)) : ℝ) * μ.1 := by
  have hsplit : ∑' a : EigenvectorIndex S, a.1.1 =
      ∑' (μ : { ν : ℝ // ν ≠ 0 }) (i : Fin (Module.finrank ℂ
        (Module.End.eigenspace (S : H →ₗ[ℂ] H) (μ.1 : ℂ)))), (⟨μ, i⟩ : EigenvectorIndex S).1.1 :=
    hS.tsum_sigma
  rw [hsplit]
  refine tsum_congr fun μ => ?_
  simp [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ContinuousLinearMap
