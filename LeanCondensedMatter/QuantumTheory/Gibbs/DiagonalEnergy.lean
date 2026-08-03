import LeanCondensedMatter.QuantumTheory.Gibbs.Entropy

/-!
# Energy expectation in a common diagonal basis

When a density operator and an observable are diagonal in the same finite orthonormal basis, their
energy expectation is the weighted sum of the corresponding diagonal values.
-/

namespace QuantumTheory

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- If `ρ` and `Hop` are diagonal in the same orthonormal basis, then
`energyExpValue ρ Hop = Σᵢ wᵢ Eᵢ`. -/
theorem energyExpValue_eq_sum_common_eigenbasis (ρ : DensityOperator H) (Hop : Observable H)
    (b : OrthonormalBasis ι ℂ H) (w E : ι → ℝ)
    (hρ : ∀ i, (ρ.op : H →ₗ[ℂ] H) (b i) = (w i : ℂ) • b i)
    (hE : ∀ i, (Hop.1 : H →ₗ[ℂ] H) (b i) = (E i : ℂ) • b i) :
    energyExpValue ρ Hop = ∑ i, w i * E i := by
  have hbase := ρ.expectation_eq_sum_diagonal Hop.1 b w hρ
  have hcomplex :
      (energyExpValue ρ Hop : ℂ) = ∑ i, ((w i * E i : ℝ) : ℂ) := by
    calc
      (energyExpValue ρ Hop : ℂ) = ρ.expectation Hop.1 :=
        (ρ.expectation_observable Hop).symm
      _ = ∑ i, (w i : ℂ) * inner ℂ (b i) (Hop.1 (b i)) := hbase
      _ = ∑ i, ((w i * E i : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        change (w i : ℂ) * inner ℂ (b i)
          ((Hop.1 : H →ₗ[ℂ] H) (b i)) = (w i * E i : ℂ)
        rw [hE i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
        norm_num
        ring
  have hre := congrArg Complex.re hcomplex
  simpa using hre

end QuantumTheory
