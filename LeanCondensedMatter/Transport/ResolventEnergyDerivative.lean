import LeanCondensedMatter.Transport.Resolvent
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.style.header false

/-!
# Real-energy derivatives of retarded and advanced resolvents

`Resolvent` proves the holomorphic spectral-parameter identity

```text
dG(z) / dz = -G(z)^2.
```

The Středa energy integral instead differentiates the real-energy paths
`E ↦ Gᴿ(E, η)` and `E ↦ Gᴬ(E, η)` at fixed positive broadening. This module derives those
real derivatives by composing the complex resolvent derivative with the affine spectral paths
`E ↦ E ± iη`.

The result remains dimension-independent and contains no trace, conductivity, zero-broadening,
or thermodynamic-limit statement.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- At fixed broadening, the retarded spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_retardedSpectralParameter_energy
    (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => retardedSpectralParameter x broadening)
      (1 : ℂ) energy := by
  fun_prop

/-- At fixed broadening, the advanced spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_advancedSpectralParameter_energy
    (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => advancedSpectralParameter x broadening)
      (1 : ℂ) energy := by
  fun_prop

/-- The retarded resolvent differentiated along the real-energy axis is `-(Gᴿ)^2`. -/
theorem hasDerivAt_retardedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa [retardedResolvent] using
    (hasDerivAt_resolvent_retarded hamiltonian hself energy broadening hbroadening).comp
      energy (hasDerivAt_retardedSpectralParameter_energy energy broadening)

/-- The advanced resolvent differentiated along the real-energy axis is `-(Gᴬ)^2`. -/
theorem hasDerivAt_advancedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa [advancedResolvent] using
    (hasDerivAt_resolvent_advanced hamiltonian hself energy broadening hbroadening).comp
      energy (hasDerivAt_advancedSpectralParameter_energy energy broadening)

namespace BoundedSystem

/-- System-level real-energy derivative of the stored-broadening retarded Green operator. -/
theorem hasDerivAt_retardedGreen_energy
    (system : BoundedSystem H) (energy : ℝ) :
    HasDerivAt system.retardedGreen
      (-(system.retardedGreen energy) ^ 2) energy := by
  simpa [retardedGreen] using
    hasDerivAt_retardedResolvent_energy system.hamiltonian.1 system.hamiltonian.2
      energy system.broadening system.broadening_pos

/-- System-level real-energy derivative of the stored-broadening advanced Green operator. -/
theorem hasDerivAt_advancedGreen_energy
    (system : BoundedSystem H) (energy : ℝ) :
    HasDerivAt system.advancedGreen
      (-(system.advancedGreen energy) ^ 2) energy := by
  simpa [advancedGreen] using
    hasDerivAt_advancedResolvent_energy system.hamiltonian.1 system.hamiltonian.2
      energy system.broadening system.broadening_pos

end BoundedSystem

end

end QuantumTheory.Transport
