import LeanCondensedMatter.Transport.Streda.TraceKernel
import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.Transport.Resolvent.Spectral

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
          exact Finset.sum_comm
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
  simp only [Finset.sum_sub_distrib]


/-- A finite real-energy spectral resolution replaces the canonical retarded
and advanced resolvents throughout the traced Bastin kernel. This is
representation-independent: model consumers need only the completeness and
diagonal Hamiltonian action of their projector family. -/
theorem regularizedBastinTraceIntegrand_eq_projectorSum
    [CompleteSpace H]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (P : ι → H →L[ℂ] H) (eigenvalue : ι → ℝ)
    (hcomplete : ∑ i, P i = 1)
    (haction : ∀ i, hamiltonian * P i = (eigenvalue i : ℂ) • P i)
    (J K : H →L[ℂ] H)
    (probeEnergy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    regularizedBastinTraceIntegrand hamiltonian J K probeEnergy broadening =
      let r := ∑ i, scalarResolventCoefficient
        (retardedSpectralParameter probeEnergy broadening) (eigenvalue i) • P i
      let a := ∑ i, scalarResolventCoefficient
        (advancedSpectralParameter probeEnergy broadening) (eigenvalue i) • P i
      finiteDimensionalOperatorTrace (H := H)
        ((J * r ^ 2 * K - K * a ^ 2 * J) * (r - a)) := by
  have hretarded :
      retardedResolvent hamiltonian probeEnergy broadening =
        ∑ i, scalarResolventCoefficient
          (retardedSpectralParameter probeEnergy broadening) (eigenvalue i) • P i := by
    simpa only [retardedResolvent, retardedSpectralParameter,
      spectralResolvent_retarded_ofRegulator, spectralParameter_retarded_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_sum
        hamiltonian hself P eigenvalue hcomplete haction
        probeEnergy broadening hbroadening
  have hadvanced :
      advancedResolvent hamiltonian probeEnergy broadening =
        ∑ i, scalarResolventCoefficient
          (advancedSpectralParameter probeEnergy broadening) (eigenvalue i) • P i := by
    simpa only [advancedResolvent, advancedSpectralParameter,
      spectralResolvent_advanced_ofRegulator, spectralParameter_advanced_ofRegulator] using
      resolvent_spectralParameterOfRegulator_eq_sum
        hamiltonian hself P eigenvalue hcomplete haction
        probeEnergy (-broadening) (neg_ne_zero.mpr hbroadening)
  unfold regularizedBastinTraceIntegrand regularizedBastinOperatorIntegrand
    retardedAdvancedResolventDifference
  rw [hretarded, hadvanced]
  congr 1
  noncomm_ring

end

end QuantumTheory.Transport
