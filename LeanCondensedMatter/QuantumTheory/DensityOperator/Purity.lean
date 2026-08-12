import LeanCondensedMatter.QuantumTheory.DensityOperator.Pure
import LeanCondensedMatter.QuantumTheory.DensityOperator.ExpectationOrder

/-!
# Purity of density operators

Purity is the sum of the squared spectral eigenvalues of the canonical density operator. This
definition is dimension-independent and uses the spectral probability distribution of the state.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The squared eigenvalue family of a density operator is summable. -/
theorem DensityOperator.summable_eigenvalue_sq (ρ : DensityOperator H) :
    Summable (fun a : EigenvectorIndex ρ.op => a.1.1 ^ 2) := by
  have heigen : Summable (fun a : EigenvectorIndex ρ.op => a.1.1) :=
    ρ.spectralTraceClass.summable.congr (fun a => abs_of_nonneg (ρ.eigenvalue_nonneg a))
  exact Summable.of_nonneg_of_le
    (fun a => sq_nonneg a.1.1)
    (fun a => by nlinarith [ρ.eigenvalue_nonneg a, ρ.eigenvalue_le_one a])
    heigen

/-- The purity of a density operator, `∑ᵢ λᵢ²`. -/
noncomputable def purity (ρ : DensityOperator H) : ℝ :=
  ∑' a : EigenvectorIndex ρ.op, a.1.1 ^ 2

/-- Purity is nonnegative. -/
theorem purity_nonneg (ρ : DensityOperator H) : 0 ≤ purity ρ := by
  rw [purity]
  exact tsum_nonneg fun a => sq_nonneg a.1.1

/-- Purity is at most one. -/
theorem purity_le_one (ρ : DensityOperator H) : purity ρ ≤ 1 := by
  have heigen : Summable (fun a : EigenvectorIndex ρ.op => a.1.1) :=
    ρ.spectralTraceClass.summable.congr (fun a => abs_of_nonneg (ρ.eigenvalue_nonneg a))
  rw [purity]
  calc
    (∑' a : EigenvectorIndex ρ.op, a.1.1 ^ 2) ≤
        ∑' a : EigenvectorIndex ρ.op, a.1.1 :=
      ρ.summable_eigenvalue_sq.tsum_mono heigen
        (fun a => by nlinarith [ρ.eigenvalue_nonneg a, ρ.eigenvalue_le_one a])
    _ = 1 := by
      have htrace := ρ.spectralTrace_op_eq_one
      change (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 at htrace
      exact htrace

/-- The expectation of the density operator itself is its purity. -/
@[simp]
theorem DensityOperator.expectation_op (ρ : DensityOperator H) :
    ρ.expectation ρ.op = (purity ρ : ℂ) := by
  have hexpect := (ρ.summable_expectation_term ρ.op).hasSum
  rw [← ρ.expectation_apply ρ.op] at hexpect
  have hpoint :
      (fun a : EigenvectorIndex ρ.op =>
        (a.1.1 : ℂ) * inner ℂ (eigenvectorFamily ρ.spectralTraceClass.compact a)
          (ρ.op (eigenvectorFamily ρ.spectralTraceClass.compact a))) =
      (fun a => ((a.1.1 ^ 2 : ℝ) : ℂ)) := by
    funext a
    have ha :
        ρ.op (eigenvectorFamily ρ.spectralTraceClass.compact a) =
          (a.1.1 : ℂ) • eigenvectorFamily ρ.spectralTraceClass.compact a := by
      simpa using apply_eigenvectorFamily ρ.spectralTraceClass.compact a
    rw [ha, inner_smul_right, inner_self_eq_norm_sq_to_K,
      eigenvectorFamily_norm_eq_one ρ a]
    norm_num
    ring
  rw [hpoint] at hexpect
  have hpurity : HasSum (fun a : EigenvectorIndex ρ.op => ((a.1.1 ^ 2 : ℝ) : ℂ))
      (purity ρ : ℂ) := by
    simpa [purity] using Complex.ofRealCLM.hasSum ρ.summable_eigenvalue_sq.hasSum
  exact hexpect.unique hpurity

/-- A rank-one density operator has purity one. -/
theorem purity_pure (ψ : State H) : purity (pure ψ) = 1 := by
  letI := uniqueEigenvectorIndexRankOne ψ.2
  change (∑' a : EigenvectorIndex
    (InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H), a.1.1 ^ 2) = 1
  rw [tsum_eq_single (uniqueEigenvectorIndexRankOne ψ.2).default (fun b hb =>
    absurd (Subsingleton.elim b (uniqueEigenvectorIndexRankOne ψ.2).default) hb)]
  have hdefault : (uniqueEigenvectorIndexRankOne ψ.2).default.1.1 = 1 := rfl
  rw [hdefault]
  norm_num

end QuantumTheory
