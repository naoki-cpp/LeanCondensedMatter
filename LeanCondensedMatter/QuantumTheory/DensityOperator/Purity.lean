import LeanCondensedMatter.QuantumTheory.DensityOperator.PureState
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

/-- Purity one forces every nonzero spectral eigenvalue of a density operator to equal one. -/
theorem DensityOperator.eigenvalue_eq_one_of_purity_eq_one
    (ρ : DensityOperator H) (hpurity : purity ρ = 1)
    (a : EigenvectorIndex ρ.op) : a.1.1 = 1 := by
  have heigen : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    ρ.spectralTraceClass.summable.congr (fun b => abs_of_nonneg (ρ.eigenvalue_nonneg b))
  have hgap : Summable (fun b : EigenvectorIndex ρ.op => b.1.1 - b.1.1 ^ 2) :=
    heigen.sub ρ.summable_eigenvalue_sq
  have hgap_nonneg : ∀ b : EigenvectorIndex ρ.op, 0 ≤ b.1.1 - b.1.1 ^ 2 := by
    intro b
    nlinarith [ρ.eigenvalue_nonneg b, ρ.eigenvalue_le_one b]
  have hgap_sum : (∑' b : EigenvectorIndex ρ.op, (b.1.1 - b.1.1 ^ 2)) = 0 := by
    rw [heigen.tsum_sub ρ.summable_eigenvalue_sq]
    have htrace := ρ.spectralTrace_op_eq_one
    change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
    rw [htrace]
    change 1 - purity ρ = 0
    rw [hpurity]
    norm_num
  have hle := hgap.le_tsum a (fun b _ => hgap_nonneg b)
  rw [hgap_sum] at hle
  have hpos : 0 < a.1.1 :=
    lt_of_le_of_ne (ρ.eigenvalue_nonneg a) (Ne.symm a.1.2)
  nlinarith [hgap_nonneg a]

private theorem eigenvectorIndex_nonempty_of_purity_eq_one
    (ρ : DensityOperator H) (hpurity : purity ρ = 1) :
    Nonempty (EigenvectorIndex ρ.op) := by
  classical
  by_contra hnonempty
  haveI : IsEmpty (EigenvectorIndex ρ.op) :=
    ⟨fun a => hnonempty ⟨a⟩⟩
  have hzero : purity ρ = 0 := by
    simp [purity]
  linarith

private theorem eigenvectorIndex_subsingleton_of_purity_eq_one
    (ρ : DensityOperator H) (hpurity : purity ρ = 1)
    (a b : EigenvectorIndex ρ.op) : a = b := by
  classical
  by_contra hab
  have hle := ρ.summable_eigenvalue_sq.sum_le_tsum ({a, b} : Finset (EigenvectorIndex ρ.op))
    (fun c _ => sq_nonneg c.1.1)
  have ha := ρ.eigenvalue_eq_one_of_purity_eq_one hpurity a
  have hb := ρ.eigenvalue_eq_one_of_purity_eq_one hpurity b
  have hsum :
      ∑ c ∈ ({a, b} : Finset (EigenvectorIndex ρ.op)), c.1.1 ^ 2 = 2 := by
    simp [hab, ha, hb]
    norm_num
  rw [hsum] at hle
  change 2 ≤ purity ρ at hle
  rw [hpurity] at hle
  norm_num at hle

/-- A density operator with purity one is a physical pure state. -/
theorem isPureDensity_of_purity_eq_one (ρ : DensityOperator H)
    (hpurity : purity ρ = 1) : IsPureDensity ρ := by
  classical
  have hnonempty := eigenvectorIndex_nonempty_of_purity_eq_one ρ hpurity
  let a0 : EigenvectorIndex ρ.op := Classical.choice hnonempty
  letI : Unique (EigenvectorIndex ρ.op) :=
    { default := a0
      uniq := fun a => eigenvectorIndex_subsingleton_of_purity_eq_one ρ hpurity a a0 }
  let ψ : StateVector H :=
    ⟨eigenvectorFamily ρ.spectralTraceClass.compact (default : EigenvectorIndex ρ.op),
      eigenvectorFamily_norm_eq_one ρ (default : EigenvectorIndex ρ.op)⟩
  refine ⟨ψ, ?_⟩
  apply DensityOperator.ext
  change ρ.op = InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  ext x
  simp only [InnerProductSpace.rankOne_apply]
  have hsum := hasSum_eigenvectorFamily
    ρ.spectralTraceClass.compact ρ.isSymmetric x
  rw [← hsum.tsum_eq]
  rw [tsum_eq_single (default : EigenvectorIndex ρ.op) (fun b hb =>
    absurd (Subsingleton.elim b (default : EigenvectorIndex ρ.op)) hb)]
  rw [ρ.eigenvalue_eq_one_of_purity_eq_one hpurity (default : EigenvectorIndex ρ.op)]
  simp [ψ]

/-- A density operator is physically pure exactly when its spectral purity is one. -/
theorem isPureDensity_iff_purity_eq_one (ρ : DensityOperator H) :
    IsPureDensity ρ ↔ purity ρ = 1 := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact purity_pure ψ
  · exact isPureDensity_of_purity_eq_one ρ

end QuantumTheory
