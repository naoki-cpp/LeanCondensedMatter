import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Spectral action of regulated resolvents

For a bounded self-adjoint Hamiltonian, a resolvent at `E + iγ` with nonzero signed regulator acts
diagonally on every Hamiltonian eigenvector. The representation-independent resolvent/eigenvector
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
      (Filter.nhds 0)
      (Filter.nhds (scalarResolventCoefficient (probeEnergy : ℂ) eigenvalue)) := by
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
      (Filter.nhds 0)
      (Filter.nhds
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

end
end Transport
end QuantumTheory
