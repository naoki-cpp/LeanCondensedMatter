import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Spectral action of regulated resolvents

For a bounded self-adjoint Hamiltonian, a resolvent at `E + iγ` with nonzero signed regulator acts
diagonally on every Hamiltonian eigenvector and admits finite projector expansions.
The representation-independent resolvent/eigenvector
theorem is owned by `Analysis.Operator.Spectral.Resolvent`; this module owns its generic regulated
transport specialization. Physical retarded/advanced branches are specialized locally by consumers
with `γ = ±η`.

No pure-point response data, trace, occupation integral, contact cancellation, zero-broadening
limit, or conductivity claim is made here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar resolvent coefficient associated with a real spectral value. This is the
representation-independent scalar factor that appears in every finite-projector resolvent. -/
noncomputable def scalarResolventCoefficient (z : ℂ) (eigenvalue : ℝ) : ℂ :=
  (z - (eigenvalue : ℂ))⁻¹

/-- The scalar resolvent coefficient is continuous wherever its spectral denominator is nonzero. -/
theorem continuousAt_scalarResolventCoefficient
    (z : ℂ) (eigenvalue : ℝ)
    (hden : z - (eigenvalue : ℂ) ≠ 0) :
    ContinuousAt (fun w : ℂ => scalarResolventCoefficient w eigenvalue) z := by
  unfold scalarResolventCoefficient
  exact (continuousAt_id.sub continuousAt_const).inv₀ hden

private theorem complex_spectral_offset_ne_zero
    (probeEnergy eigenvalue : ℝ) (hprobe : probeEnergy ≠ eigenvalue) :
    (((probeEnergy - eigenvalue : ℝ) : ℂ)) ≠ 0 := by
  exact_mod_cast sub_ne_zero.mpr hprobe

/-- Away from a real spectral pole, the side-indexed regulated scalar coefficient converges to the
ordinary real-energy scalar resolvent as the broadening tends to zero. -/
theorem tendsto_scalarResolventCoefficient_spectralParameter_zero
    (side : SpectralSide) (probeEnergy eigenvalue : ℝ)
    (hprobe : probeEnergy ≠ eigenvalue) :
    Filter.Tendsto
      (fun broadening : ℝ =>
        scalarResolventCoefficient
          (spectralParameter side probeEnergy broadening) eigenvalue)
      (nhds 0)
      (nhds (scalarResolventCoefficient (probeEnergy : ℂ) eigenvalue)) := by
  have hden :
      spectralParameter side probeEnergy 0 - (eigenvalue : ℂ) ≠ 0 := by
    simpa [spectralParameter, spectralParameterOfRegulator, SpectralSide.regulator] using
      complex_spectral_offset_ne_zero probeEnergy eigenvalue hprobe
  have hcontinuous : ContinuousAt
      (fun broadening : ℝ =>
        spectralParameter side probeEnergy broadening - (eigenvalue : ℂ)) 0 := by
    unfold spectralParameter spectralParameterOfRegulator SpectralSide.regulator
    fun_prop
  have hinv : Filter.Tendsto
      (fun broadening : ℝ =>
        (spectralParameter side probeEnergy broadening - (eigenvalue : ℂ))⁻¹)
      (nhds 0)
      (nhds
        ((spectralParameter side probeEnergy 0 - (eigenvalue : ℂ))⁻¹)) :=
    (hcontinuous.inv₀ hden).tendsto
  simpa [scalarResolventCoefficient, spectralParameter, spectralParameterOfRegulator,
    SpectralSide.regulator] using hinv

/-- A resolvent with arbitrary nonzero signed regulator acts on a Hamiltonian eigenvector by the
corresponding scalar resolvent factor. -/
theorem resolvent_spectralParameterOfRegulator_apply_eigenvector
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    {v : H} {eigenvalue : ℝ}
    (hv : hamiltonian v = (eigenvalue : ℂ) • v)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) v =
      (spectralParameterOfRegulator energy regulator - (eigenvalue : ℂ))⁻¹ • v := by
  apply QuantumTheory.resolvent_apply_eigenvector
  · exact QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
        (by
          rw [spectralParameterOfRegulator_im]
          exact hregulator)
  · exact spectralParameterOfRegulator_sub_real_ne_zero
      energy regulator eigenvalue hregulator
  · exact hv

/-- A finite real-energy projector expansion equals the canonical resolvent at every nonzero
signed regulator. Model adapters supply only completeness and the Hamiltonian's diagonal action. -/
theorem resolvent_spectralParameterOfRegulator_eq_sum
    {ι : Type*} [Fintype ι]
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (P : ι → H →L[ℂ] H) (eigenvalue : ι → ℝ)
    (hcomplete : ∑ i, P i = 1)
    (haction : ∀ i, hamiltonian * P i = (eigenvalue i : ℂ) • P i)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) =
      ∑ i, scalarResolventCoefficient
        (spectralParameterOfRegulator energy regulator) (eigenvalue i) • P i := by
  apply QuantumTheory.resolvent_eq_sum_inv_smul_of_diagonal_action
    hamiltonian P (fun i => (eigenvalue i : ℂ)) hcomplete haction
  · apply QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself
    rw [spectralParameterOfRegulator_im]
    exact hregulator
  · intro i
    exact spectralParameterOfRegulator_sub_real_ne_zero energy regulator (eigenvalue i) hregulator

end
end Transport
end QuantumTheory
