import LeanCondensedMatter.Analysis.Operator.Spectral.EigenvectorFamily
import Mathlib.Analysis.Normed.Operator.Compact.Basic

set_option linter.style.header false

/-!
# Spectral summability and spectral trace for compact self-adjoint operators

Defines `HasSummableRealEigenvalues` and its associated `spectralTrace` on top of
`EigenvectorFamily.lean`'s `EigenvectorIndex`.

These declarations are not a general trace-class ideal: the predicate records only absolute
summability of the indexed nonzero real eigenvalues. Compactness and symmetry remain explicit
hypotheses of the operator theorems that use the spectral expansion. See
`notes/roadmaps/operator-algebra.md`.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

variable {T : H →L[ℂ] H}

omit [CompleteSpace H] in
/-- Rank-one operators on a Hilbert space are compact. -/
theorem isCompactOperator_rankOne (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y : H →L[ℂ] H) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ y)).clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ x)

/-- The absolute values of the indexed nonzero real eigenvalues of `T`, with multiplicity, are
summable.

For the compact self-adjoint operators used by this project, this is the spectral summability
condition underlying spectral-trace arguments. The predicate itself deliberately does **not** assert
compactness or symmetry; those hypotheses are supplied separately wherever the spectral theorem is
used.

No separate "independent of the choice of eigenbasis" lemma is needed here: `EigenvectorIndex T`
and the eigenvalue recorded at each index (`a.1.1`) depend only on the eigenspaces of `T` and their
dimensions, not on which orthonormal basis `stdOrthonormalBasis` happens to pick within each
(possibly multi-dimensional) eigenspace. -/
def HasSummableRealEigenvalues (T : H →L[ℂ] H) : Prop :=
  Summable (fun a : EigenvectorIndex T => |a.1.1|)

/-- The (totalized) spectral sum of the indexed nonzero real eigenvalues of `T`, with
multiplicity.  As for Mathlib's `tsum`, this definition is available for every operator; theorems
that identify or manipulate the sum state `HasSummableRealEigenvalues T` explicitly. -/
noncomputable def spectralTrace (T : H →L[ℂ] H) : ℝ :=
  ∑' a : EigenvectorIndex T, a.1.1

omit [CompleteSpace H] in
/-- Every eigenvalue of a positive operator is nonnegative. -/
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
/-- The spectral trace of a positive spectrally summable operator is nonnegative. -/
theorem trace_nonneg {T : H →L[ℂ] H}
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) : 0 ≤ spectralTrace T :=
  tsum_nonneg fun a => eigenvalue_nonneg_of_isPositive hpos a

omit [CompleteSpace H] in
theorem summable_eigenvectorIndex {S : H →L[ℂ] H} (hS : HasSummableRealEigenvalues S) :
    Summable (fun a : EigenvectorIndex S => a.1.1) := by
  have hS' : Summable (fun a : EigenvectorIndex S => |a.1.1|) := hS
  exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using hS')

omit [CompleteSpace H] in
/-- Splits the spectral-trace `tsum` over `EigenvectorIndex S` into an outer sum over the
base nonzero eigenvalues and an inner finite sum over each eigenspace's basis vectors. -/
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
