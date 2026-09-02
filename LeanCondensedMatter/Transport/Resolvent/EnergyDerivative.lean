import LeanCondensedMatter.Transport.Resolvent.Basic
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.style.header false

/-!
# Real-energy derivatives of retarded and advanced resolvents

The representation-independent holomorphic identity

```text
dG(z) / dz = -G(z)^2
```

is owned by `Analysis.Operator.Spectral.Resolvent`. The Středa energy integral instead
differentiates real-energy paths at fixed imaginary regulator. This module first records that the
signed-regulator spectral parameter `E ↦ E + iγ` has derivative one, then specializes to the
physical side-indexed paths `E ↦ Gˢ(E, η)` and retains the conventional retarded/advanced names.

The result remains dimension-independent and contains no trace, conductivity, zero-broadening,
or thermodynamic-limit statement.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Along the real-energy axis, a spectral parameter with fixed signed regulator has derivative one. -/
theorem hasDerivAt_spectralParameterOfRegulator_energy
    (energy regulator : ℝ) :
    HasDerivAt (fun x : ℝ => spectralParameterOfRegulator x regulator)
      (1 : ℂ) energy := by
  simpa [spectralParameterOfRegulator] using
    (Complex.ofRealCLM.hasDerivAt.add_const ((regulator : ℂ) * Complex.I))

/-- Along the real-energy axis, the side-indexed spectral parameter has derivative one. -/
theorem hasDerivAt_spectralParameter_energy
    (side : SpectralSide) (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => spectralParameter side x broadening)
      (1 : ℂ) energy := by
  simpa [spectralParameter] using
    hasDerivAt_spectralParameterOfRegulator_energy energy (side.sign * broadening)

/-- A spectral resolvent differentiated along the real-energy axis is `-Gˢ²`. -/
theorem hasDerivAt_spectralResolvent_energy
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    HasDerivAt
      (fun x : ℝ => spectralResolvent side hamiltonian x broadening)
      (-(spectralResolvent side hamiltonian energy broadening) ^ 2)
      energy := by
  have hresolvent :
      HasDerivAt (resolvent hamiltonian)
        (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
        (spectralParameter side energy broadening) := by
    exact spectrum.hasDerivAt_resolvent_const_left
      (spectrum.notMem_iff.mp
        (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
          hamiltonian hself (spectralParameter side energy broadening)
          (by
            rw [spectralParameter_im]
            exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)))
  have hcomp := hresolvent.scomp
    energy (hasDerivAt_spectralParameter_energy side energy broadening)
  change HasDerivAt
    (resolvent hamiltonian ∘ fun x : ℝ => spectralParameter side x broadening)
    (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
    energy
  simpa only [one_smul] using hcomp

/-- The retarded resolvent differentiated along the real-energy axis is `-(Gᴿ)^2`. -/
theorem hasDerivAt_retardedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa only [spectralResolvent_retarded] using
    hasDerivAt_spectralResolvent_energy
      .retarded hamiltonian hself energy broadening (ne_of_gt hbroadening)

/-- The advanced resolvent differentiated along the real-energy axis is `-(Gᴬ)^2`. -/
theorem hasDerivAt_advancedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa only [spectralResolvent_advanced] using
    hasDerivAt_spectralResolvent_energy
      .advanced hamiltonian hself energy broadening (ne_of_gt hbroadening)

/-- At fixed nonzero broadening, either spectral-side resolvent is continuous along the real-energy
axis. -/
theorem continuous_spectralResolvent_energy
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Continuous (fun energy : ℝ => spectralResolvent side hamiltonian energy broadening) := by
  rw [continuous_iff_continuousAt]
  intro energy
  exact
    (hasDerivAt_spectralResolvent_energy
      side hamiltonian hself energy broadening hbroadening).continuousAt

/-- At fixed positive broadening, the retarded resolvent is continuous along the real-energy axis. -/
theorem continuous_retardedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ => retardedResolvent hamiltonian energy broadening) := by
  simpa only [spectralResolvent_retarded] using
    continuous_spectralResolvent_energy .retarded hamiltonian hself broadening
      (ne_of_gt hbroadening)

/-- At fixed positive broadening, the advanced resolvent is continuous along the real-energy axis. -/
theorem continuous_advancedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (broadening : ℝ) (hbroadening : 0 < broadening) :
    Continuous (fun energy : ℝ => advancedResolvent hamiltonian energy broadening) := by
  simpa only [spectralResolvent_advanced] using
    continuous_spectralResolvent_energy .advanced hamiltonian hself broadening
      (ne_of_gt hbroadening)

end

end QuantumTheory.Transport
