import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary.Operator
import LeanCondensedMatter.Analysis.Operator.FiniteTrace

set_option linter.style.header false

/-!
# Ordinary finite-dimensional trace under antiunitary conjugation

The trace of an operator conjugated by an antiunitary equals the complex
conjugate of its original trace. The proof transports an orthonormal
basis along the antiunitary, without requiring a same-label eigenbasis
pairing, nor requiring the antiunitary to square to the identity.
-/

namespace QuantumTheory.LinearResponse

open ContinuousLinearMap

noncomputable section

namespace AntiunitaryMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [FiniteDimensional ℂ H]
variable (Θ : AntiunitaryMap H)

/-- The ordinary finite-dimensional trace is conjugated by the induced
operator action of any antiunitary on the Hilbert space. -/
theorem conjugateOperator_trace (A : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (Θ.conjugateOperator A) =
      star (finiteDimensionalOperatorTrace A) := by
  classical
  let b := stdOrthonormalBasis ℂ H
  have horth : Orthonormal ℂ (fun i => Θ.equiv (b i)) := by
    apply (orthonormal_iff_ite).2
    intro i j
    rw [Θ.inner_map, (orthonormal_iff_ite).1 b.orthonormal i j]
    split_ifs <;> simp
  have horth' :
      Orthonormal ℂ
        ((Set.univ : Set (Fin (Module.finrank ℂ H))).domRestrict
          (fun i => Θ.equiv (b i))) := by
    change Orthonormal ℂ
      (fun i : (Set.univ : Set (Fin (Module.finrank ℂ H))) => Θ.equiv (b i))
    exact horth.comp
      (fun i : (Set.univ : Set (Fin (Module.finrank ℂ H))) => (i : Fin (Module.finrank ℂ H)))
      Subtype.val_injective
  obtain ⟨b', hb'⟩ :=
    horth'.exists_orthonormalBasis_extension_of_card_eq
      (Module.finrank_eq_card_basis b.toBasis)
  have hb' (i) : b' i = Θ.equiv (b i) := hb' i (Set.mem_univ i)
  rw [finiteDimensionalOperatorTrace_apply, finiteDimensionalOperatorTrace_apply,
    LinearMap.trace_eq_sum_inner _ b', LinearMap.trace_eq_sum_inner _ b, star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb' i]
  change inner ℂ (Θ.equiv (b i))
      (Θ.equiv (A (Θ.equiv.symm (Θ.equiv (b i))))) =
    (starRingEnd ℂ) (inner ℂ (b i) (A (b i)))
  rw [Θ.equiv.symm_apply_apply]
  exact Θ.inner_map (b i) (A (b i))

end AntiunitaryMap

end
end QuantumTheory.LinearResponse
