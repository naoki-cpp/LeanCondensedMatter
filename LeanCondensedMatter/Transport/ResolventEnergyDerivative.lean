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
  simpa [retardedSpectralParameter] using
    (Complex.ofRealCLM.hasDerivAt.add_const ((broadening : ℂ) * Complex.I))

/-- At fixed broadening, the advanced spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_advancedSpectralParameter_energy
    (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => advancedSpectralParameter x broadening)
      (1 : ℂ) energy := by
  simpa [advancedSpectralParameter, sub_eq_add_neg] using
    (Complex.ofRealCLM.hasDerivAt.add_const (-((broadening : ℂ) * Complex.I)))

/-- The retarded resolvent differentiated along the real-energy axis is `-(Gᴿ)^2`. -/
theorem hasDerivAt_retardedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
  have houter : HasFDerivAt (resolvent hamiltonian)
      ((ContinuousLinearMap.smulRight 1
        (-(retardedResolvent hamiltonian energy broadening) ^ 2) :
          ℂ →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ)
      (retardedSpectralParameter energy broadening) :=
    (hasDerivAt_resolvent_retarded hamiltonian hself energy broadening hbroadening).hasFDerivAt
      |>.restrictScalars ℝ
  have hinner :=
    (hasDerivAt_retardedSpectralParameter_energy energy broadening).hasFDerivAt
  have hcomp := (houter.comp energy hinner).hasDerivAt
  have hvalue :
      ((ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight 1
            (-(retardedResolvent hamiltonian energy broadening) ^ 2)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ 1) 1) =
        -(retardedResolvent hamiltonian energy broadening) ^ 2 := by
    change (1 : ℂ) • (-(retardedResolvent hamiltonian energy broadening) ^ 2) = _
    simp
  rw [hvalue] at hcomp
  change HasDerivAt
    (resolvent hamiltonian ∘ fun x : ℝ => retardedSpectralParameter x broadening)
    (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy
  exact hcomp

/-- The advanced resolvent differentiated along the real-energy axis is `-(Gᴬ)^2`. -/
theorem hasDerivAt_advancedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
  have houter : HasFDerivAt (resolvent hamiltonian)
      ((ContinuousLinearMap.smulRight 1
        (-(advancedResolvent hamiltonian energy broadening) ^ 2) :
          ℂ →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ)
      (advancedSpectralParameter energy broadening) :=
    (hasDerivAt_resolvent_advanced hamiltonian hself energy broadening hbroadening).hasFDerivAt
      |>.restrictScalars ℝ
  have hinner :=
    (hasDerivAt_advancedSpectralParameter_energy energy broadening).hasFDerivAt
  have hcomp := (houter.comp energy hinner).hasDerivAt
  have hvalue :
      ((ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.smulRight 1
            (-(advancedResolvent hamiltonian energy broadening) ^ 2)) ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ 1) 1) =
        -(advancedResolvent hamiltonian energy broadening) ^ 2 := by
    change (1 : ℂ) • (-(advancedResolvent hamiltonian energy broadening) ^ 2) = _
    simp
  rw [hvalue] at hcomp
  change HasDerivAt
    (resolvent hamiltonian ∘ fun x : ℝ => advancedSpectralParameter x broadening)
    (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy
  exact hcomp

namespace BoundedSystem

/-- System-level real-energy derivative of the stored-broadening retarded Green operator. -/
theorem hasDerivAt_retardedGreen_energy
    (system : BoundedSystem H) (energy : ℝ) :
    HasDerivAt system.retardedGreen
      (-(system.retardedGreen energy) ^ 2) energy := by
  change HasDerivAt
    (fun x : ℝ => retardedResolvent system.hamiltonian.1 x system.broadening)
    (-(retardedResolvent system.hamiltonian.1 energy system.broadening) ^ 2) energy
  exact hasDerivAt_retardedResolvent_energy system.hamiltonian.1 system.hamiltonian.2
    energy system.broadening system.broadening_pos

/-- System-level real-energy derivative of the stored-broadening advanced Green operator. -/
theorem hasDerivAt_advancedGreen_energy
    (system : BoundedSystem H) (energy : ℝ) :
    HasDerivAt system.advancedGreen
      (-(system.advancedGreen energy) ^ 2) energy := by
  change HasDerivAt
    (fun x : ℝ => advancedResolvent system.hamiltonian.1 x system.broadening)
    (-(advancedResolvent system.hamiltonian.1 energy system.broadening) ^ 2) energy
  exact hasDerivAt_advancedResolvent_energy system.hamiltonian.1 system.hamiltonian.2
    energy system.broadening system.broadening_pos

end BoundedSystem

end

end QuantumTheory.Transport
