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
  have hdiag (i : ι) :
      (inner ℂ (b i) ((ρ.op ∘L Hop.1) (b i)) : ℂ).re = w i * E i := by
    change (inner ℂ (b i)
      ((ρ.op : H →ₗ[ℂ] H) ((Hop.1 : H →ₗ[ℂ] H) (b i))) : ℂ).re = w i * E i
    have hrho := congrArg (fun x : H => (ρ.op : H →ₗ[ℂ] H) x) (hE i)
    rw [hrho, map_smul, hρ i, smul_smul, inner_smul_right,
      inner_self_eq_norm_sq_to_K, b.norm_eq_one]
    simp
    ring
  rw [energyExpValue_eq_re_linearMap_trace]
  rw [LinearMap.trace_eq_sum_inner
    ((ρ.op ∘L Hop.1 : H →L[ℂ] H) : H →ₗ[ℂ] H) b]
  calc
    (∑ i, inner ℂ (b i) ((ρ.op ∘L Hop.1) (b i))).re =
        ∑ i, (inner ℂ (b i) ((ρ.op ∘L Hop.1) (b i)) : ℂ).re := by
      simpa only [Complex.reCLM_apply] using
        (map_sum Complex.reCLM
          (fun i => inner ℂ (b i) ((ρ.op ∘L Hop.1) (b i))) Finset.univ)
    _ = ∑ i, w i * E i := Finset.sum_congr rfl fun i _ => hdiag i

end QuantumTheory
