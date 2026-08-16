import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.Gibbs.Entropy

/-!
# Energy expectation in a common diagonal basis

When a density operator and a bounded Hamiltonian are diagonal in the same Hilbert basis, their
energy expectation is the absolutely convergent `tsum` of the corresponding weights and energies.
-/

noncomputable section

namespace QuantumTheory

open ContinuousLinearMap

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If `ρ` and `Hop` are diagonal in the same Hilbert basis, then
`energyExpValue ρ Hop = ∑' i, w i * E i`. The series is absolutely convergent through the generic
Hilbert–Schmidt diagonal-expectation theorem. -/
theorem energyExpValue_eq_tsum_common_eigenbasis (ρ : DensityOperator H) (Hop : Observable H)
    (b : HilbertBasis ι ℂ H) (w E : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hE : ∀ i, Hop.1 (b i) = (E i : ℂ) • b i) :
    energyExpValue ρ Hop = ∑' i, w i * E i := by
  rw [energyExpValue_eq_observableExpectation,
    ρ.observableExpectation_eq_tsum_diagonal Hop b w hρ]
  apply tsum_congr
  intro i
  have hdiag : diagonalExpectationValue Hop.1 Hop.2 (b i) = E i := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hE i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [hdiag]

end QuantumTheory
