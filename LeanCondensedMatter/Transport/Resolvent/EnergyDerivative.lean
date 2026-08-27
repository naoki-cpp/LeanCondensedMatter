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
derivative and continuity theorem for `spectralResolvent`, then retains the conventional
retarded/advanced names as specializations.

The result remains dimension-independent and contains no trace, conductivity, zero-broadening,
or thermodynamic-limit statement.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem hasDerivAt_spectralParameter_energy
    (side : SpectralSide) (energy broadening : ℝ) :
    HasDerivAt (fun x : ℝ => spectralParameter side x broadening)
      (1 : ℂ) energy := by
  simpa [spectralParameter] using
    (Complex.ofRealCLM.hasDerivAt.add_const
      (((side.sign * broadening : ℝ) : ℂ) * Complex.I))

/-- A spectral resolvent differentiated along the real-energy axis is `-Gˢ²`. -/
theorem hasDerivAt_spectralResolvent_energy
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    HasDerivAt
      (fun x : ℝ => spectralResolvent side hamiltonian x broadening)
      (-(spectralResolvent side hamiltonian energy broadening) ^ 2)
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
  simpa only [spectralResolvent] using hcomp

/-- Compatibility name for the side-indexed real-energy derivative written with the generic
`resolvent` and `spectralParameter` expressions. -/
theorem hasDerivAt_resolvent_spectralParameter_energy
    (side : SpectralSide)
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    HasDerivAt
      (fun x : ℝ => resolvent hamiltonian (spectralParameter side x broadening))
      (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
      energy := by
  simpa only [spectralResolvent] using
    hasDerivAt_spectralResolvent_energy
      side hamiltonian hself energy broadening hbroadening

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
