import LeanCondensedMatter.Transport.Resolvent.Basic
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.style.header false

/-!
# Real-energy derivatives of retarded and advanced resolvents

`Resolvent.Basic` proves the holomorphic spectral-parameter identity

```text
dG(z) / dz = -G(z)^2.
```

The Středa energy integral instead differentiates the real-energy paths
`E ↦ Gˢ(E, η)` at fixed nonzero broadening. This module derives the common side-indexed real
derivative by composing the complex resolvent derivative with the affine spectral path
`E ↦ E + s iη`, then retains the conventional retarded/advanced names as specializations.

The result remains dimension-independent and contains no trace, conductivity, zero-broadening,
or thermodynamic-limit statement.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- At fixed broadening, every side-indexed spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_spectralParameter_energy
    (side : SpectralSide) (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => spectralParameter side x broadening)
      (1 : ℂ) energy := by
  simpa [spectralParameter] using
    (Complex.ofRealCLM.hasDerivAt.add_const
      (((side.sign * broadening : ℝ) : ℂ) * Complex.I))

/-- At fixed broadening, the retarded spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_retardedSpectralParameter_energy
    (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => retardedSpectralParameter x broadening)
      (1 : ℂ) energy := by
  simpa only [spectralParameter_retarded] using
    hasDerivAt_spectralParameter_energy .retarded energy broadening

/-- At fixed broadening, the advanced spectral parameter has real-energy derivative one. -/
theorem hasDerivAt_advancedSpectralParameter_energy
    (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => advancedSpectralParameter x broadening)
      (1 : ℂ) energy := by
  simpa only [spectralParameter_advanced] using
    hasDerivAt_spectralParameter_energy .advanced energy broadening

/-- A resolvent on either spectral side differentiated along the real-energy axis is `-Gˢ²`. -/
theorem hasDerivAt_resolvent_spectralParameter_energy
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    HasDerivAt
      (fun x : ℝ => resolvent hamiltonian (spectralParameter side x broadening))
      (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
      energy := by
  have houter : HasFDerivAt (resolvent hamiltonian)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2) :
          ℂ →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ)
      (spectralParameter side energy broadening) :=
    (hasDerivAt_resolvent_spectralParameter
      side hamiltonian hself energy broadening hbroadening).hasFDerivAt
      |>.restrictScalars ℝ
  have hinner :=
    (hasDerivAt_spectralParameter_energy side energy broadening).hasFDerivAt
  have hcomp := (houter.comp energy hinner).hasDerivAt
  have hvalue :
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2) :
            ℂ →L[ℂ] (H →L[ℂ] H)).restrictScalars ℝ ∘SL
        ContinuousLinearMap.toSpanSingleton ℝ (1 : ℂ)) 1) =
        -(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2 := by
    simp
  rw [hvalue] at hcomp
  change HasDerivAt
    (resolvent hamiltonian ∘ fun x : ℝ => spectralParameter side x broadening)
    (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
    energy
  exact hcomp

/-- The retarded resolvent differentiated along the real-energy axis is `-(Gᴿ)^2`. -/
theorem hasDerivAt_retardedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => retardedResolvent hamiltonian x broadening)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa only [retardedResolvent, spectralParameter_retarded] using
    hasDerivAt_resolvent_spectralParameter_energy
      .retarded hamiltonian hself energy broadening (ne_of_gt hbroadening)

/-- The advanced resolvent differentiated along the real-energy axis is `-(Gᴬ)^2`. -/
theorem hasDerivAt_advancedResolvent_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (fun x : ℝ => advancedResolvent hamiltonian x broadening)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2) energy := by
  simpa only [advancedResolvent, spectralParameter_advanced] using
    hasDerivAt_resolvent_spectralParameter_energy
      .advanced hamiltonian hself energy broadening (ne_of_gt hbroadening)

end

end QuantumTheory.Transport
