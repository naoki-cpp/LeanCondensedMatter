import LeanCondensedMatter.Transport.Streda.TraceKernel
import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent

set_option linter.style.header false

/-!
# Finite-projector expansion of the Bastin trace

The expansion of a finite-broadening Bastin trace into ordered source/target
projector blocks depends only on an orthogonal family of idempotents and
ordinary finite-dimensional trace cyclicity. No Hamiltonian, eigenvector
gauge, band geometry, occupation, conductivity normalization, or limiting
procedure enters this algebraic theorem.

Concrete models supply their spectral projectors and scalar resolvent
coefficients. The identity holds for any finite index type, not just two
bands.
-/

namespace QuantumTheory.Transport

noncomputable section

open ContinuousLinearMap

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H] [Fintype ι]

/-- Expand a traced product containing two independently weighted finite
projector sums. Moving the terminal projector to the front uses ordinary
finite-dimensional cyclicity, not any assumption on the projectors. -/
private theorem finiteProjectorTraceDoubleSum
    (P : ι → H →L[ℂ] H) (c d : ι → ℂ)
    (J K : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H)
        (J * (∑ s, c s • P s) * K * (∑ t, d t • P t)) =
      ∑ s, ∑ t, c s * d t *
        finiteDimensionalOperatorTrace (H := H) (P t * J * P s * K) := by
  calc
    finiteDimensionalOperatorTrace (H := H)
        (J * (∑ s, c s • P s) * K * (∑ t, d t • P t)) =
      ∑ s, ∑ t, finiteDimensionalOperatorTrace (H := H)
        (J * (c s • P s) * K * (d t • P t)) := by
          simp only [Finset.mul_sum, Finset.sum_mul, map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      calc
        finiteDimensionalOperatorTrace (H := H)
            (J * (c s • P s) * K * (d t • P t)) =
          c s * d t * finiteDimensionalOperatorTrace (H := H)
            (J * P s * K * P t) := by
              simp only [mul_smul_comm, smul_mul_assoc, smul_smul,
                map_smul, smul_eq_mul, mul_assoc]
              ring
        _ = c s * d t * finiteDimensionalOperatorTrace (H := H)
            (P t * J * P s * K) := by
              rw [show J * P s * K * P t = (J * P s * K) * P t by
                simp only [mul_assoc]]
              rw [finiteDimensionalOperatorTrace_mul_comm (J * P s * K) (P t)]
              simp only [mul_assoc]

/-- The finite-broadening projector Bastin trace is an exact sum of ordered
source/target band blocks. Neither completeness nor band energies are needed;
orthogonal idempotence is sufficient to square the spectral sums. -/
theorem finiteProjectorBastinTrace_eq_band_sum
    (P : ι → H →L[ℂ] H) (hP : OrthogonalIdempotents P)
    (r a : ι → ℂ) (J K : H →L[ℂ] H) :
    finiteDimensionalOperatorTrace (H := H)
      ((J * (∑ s, r s • P s) ^ 2 * K -
          K * (∑ s, a s • P s) ^ 2 * J) *
        ((∑ t, r t • P t) - (∑ t, a t • P t))) =
      ∑ s, ∑ t,
        r s ^ 2 * (r t - a t) *
            finiteDimensionalOperatorTrace (H := H) (P t * J * P s * K) -
          a s ^ 2 * (r t - a t) *
            finiteDimensionalOperatorTrace (H := H) (P t * K * P s * J) := by
  have hdiff :
      (∑ t, r t • P t) - (∑ t, a t • P t) =
        ∑ t, (r t - a t) • P t := by
    rw [← Finset.sum_sub_distrib]
    simp only [sub_smul]
  rw [QuantumTheory.sum_smul_sq_of_orthogonalIdempotents P hP r,
    QuantumTheory.sum_smul_sq_of_orthogonalIdempotents P hP a, hdiff]
  rw [sub_mul, map_sub]
  rw [finiteProjectorTraceDoubleSum P (fun s => r s ^ 2) (fun t => r t - a t) J K,
    finiteProjectorTraceDoubleSum P (fun s => a s ^ 2) (fun t => r t - a t) K J]
  simp only [← Finset.sum_sub_distrib]

end

end QuantumTheory.Transport
