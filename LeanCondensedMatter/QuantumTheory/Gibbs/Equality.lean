import LeanCondensedMatter.QuantumTheory.Gibbs.Variational
import LeanCondensedMatter.Analysis.Operator.TraceClass.Equality

/-!
# Equality cases for Gibbs variational inequalities

This file isolates the operator-positivity steps needed to characterize equality in the bounded
Gibbs–Klein free-energy bound. The scalar Gibbs inequality and its equality case are owned by
`FreeEnergy.lean`, next to the countable summation lemmas shared by bounded and pure-point proofs.
-/

namespace QuantumTheory

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Gibbs operator has a strictly positive diagonal matrix element on every unit vector.

The conclusion uses the complex positive order directly: it asserts both that the matrix element is
real and that its real value is strictly positive, rather than merely projecting it with `.re`. -/
theorem gibbsOp_diagonal_pos_of_norm_eq_one (Hop : Observable H) (β : ℝ) (v : H)
    (hv : ‖v‖ = 1) :
    (0 : ℂ) < inner ℂ v (gibbsOp Hop β v) := by
  rw [lt_iff_le_and_ne]
  refine ⟨(gibbsOp_isPositive Hop β).inner_nonneg_right v, ?_⟩
  intro hzero
  have hpb := exp_neg_beta_energy_le_gibbs_diagonal Hop β v hv
  have hdiag_zero :
      diagonalExpectationValue
        (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v = 0 := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right]
    exact hzero.symm
  rw [hdiag_zero] at hpb
  exact (not_le_of_gt (Real.exp_pos _)) (by simpa using hpb)

/-- If an orthonormal family saturates the Gibbs spectral trace, its span has trivial orthogonal
complement. -/
theorem gibbsOp_orthogonal_span_eq_bot_of_diagonal_sum_eq_spectralTrace
    (Hop : Observable H) (β : ℝ)
    (hcompact : IsCompactOperator (gibbsOp Hop β))
    {ι : Type*} {d : ι → H} (hd : Orthonormal ℂ d)
    (heq : ∑' i, diagonalExpectationValue
        (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint (d i) =
      spectralTrace (gibbsOp Hop β)) :
    (Submodule.span ℂ (Set.range d))ᗮ = ⊥ := by
  let htrace := gibbsOp_spectralTraceClass Hop β hcompact
  apply
    ContinuousLinearMap.orthogonal_span_eq_bot_of_sum_diagonalExpectationValue_eq_spectralTrace
      htrace.compact (gibbsOp_isPositive Hop β) htrace.summable hd ?_ heq
  intro v hv
  have hpos := gibbsOp_diagonal_pos_of_norm_eq_one Hop β v hv
  rw [← coe_diagonalExpectationValue_right
    (gibbsOp Hop β) (gibbsOp_isPositive Hop β).isSelfAdjoint v] at hpos
  exact_mod_cast hpos

end QuantumTheory
