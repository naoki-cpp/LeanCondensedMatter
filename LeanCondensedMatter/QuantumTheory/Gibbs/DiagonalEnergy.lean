import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.Gibbs.Entropy

/-!
# Energy expectation in a common diagonal basis

When a density operator and a bounded Hamiltonian are diagonal in the same Hilbert basis, their
energy expectation is the absolutely convergent `tsum` of the corresponding weights and energies.
The finite-dimensional finite-sum formula is a corollary of this dimension-independent theorem.
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
  change ρ.observableExpectation Hop = ∑' i, w i * E i
  rw [ρ.observableExpectation_eq_tsum_diagonal Hop b w hρ]
  apply tsum_congr
  intro i
  have hdiag : diagonalExpectationValue Hop.1 Hop.2 (b i) = E i := by
    apply Complex.ofReal_injective
    rw [coe_diagonalExpectationValue_right, hE i, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  rw [hdiag]

section FiniteOutcomes

variable [Fintype ι]

/-- For a finite orthonormal basis, the countable common-eigenbasis theorem reduces to the ordinary
finite weighted sum. -/
theorem energyExpValue_eq_sum_common_eigenbasis (ρ : DensityOperator H) (Hop : Observable H)
    (b : OrthonormalBasis ι ℂ H) (w E : ι → ℝ)
    (hρ : ∀ i, (ρ.op : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i)
    (hE : ∀ i, (Hop.1 : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i) :
    energyExpValue ρ Hop = ∑ i, w i * E i := by
  simpa using energyExpValue_eq_tsum_common_eigenbasis ρ Hop b.toHilbertBasis w E
    (fun i => by simpa using hρ i) (fun i => by simpa using hE i)

end FiniteOutcomes

end QuantumTheory
