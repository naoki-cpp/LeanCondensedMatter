import LeanCondensedMatter.Transport.Streda.TraceKernel
import LeanCondensedMatter.Transport.Resolvent.Spectral

set_option linter.style.header false

/-!
# Finite-projector spectral realization of the Bastin trace

The operator kernel is shared by concrete models. A complete finite spectral
resolution replaces the canonical retarded/advanced Green operators by projector
resolvents. Only completeness, the Hamiltonian's diagonal action, and self-adjointness
are required; no eigenvector gauge or model-specific band geometry enters.
-/

namespace QuantumTheory.Transport

noncomputable section

open ContinuousLinearMap

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H] [Fintype ι]

/-- Bastin operator polynomial for supplied retarded and advanced propagators.
Concrete models provide their currents and spectral projector resolvents. -/
noncomputable def bastinOperatorKernelFromPropagators
    (J K retarded advanced : H →L[ℂ] H) : H →L[ℂ] H :=
  (J * retarded ^ 2 * K - K * advanced ^ 2 * J) * (retarded - advanced)

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
  have hside (side : SpectralSide) :
      spectralResolvent side hamiltonian probeEnergy broadening =
        ∑ i, scalarResolventCoefficient
          (spectralParameter side probeEnergy broadening) (eigenvalue i) • P i := by
    simpa only [spectralResolvent, spectralParameter] using
      (resolvent_spectralParameterOfRegulator_eq_sum
        hamiltonian hself P eigenvalue hcomplete haction
        probeEnergy (side.regulator broadening) (side.regulator_ne_zero hbroadening))
  unfold regularizedBastinTraceIntegrand regularizedBastinOperatorIntegrand
    retardedAdvancedResolventDifference retardedResolvent advancedResolvent
    retardedSpectralParameter advancedSpectralParameter
  rw [hside .retarded, hside .advanced]
  congr 1
  noncomm_ring

end

end QuantumTheory.Transport
