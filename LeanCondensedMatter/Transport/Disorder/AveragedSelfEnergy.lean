import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy

set_option linter.style.header false

/-!
# Exact averaged Green / self-energy bridge

This module connects the exact finite-disorder averaged Green operator to the abstract two-sided
Dyson self-energy relation, but only when a two-sided inverse of the averaged Green operator is
supplied explicitly.

No unconditional `exactAveragedSelfEnergy` is defined: even though every configuration resolvent is
invertible at nonzero broadening, its finite disorder average need not be invertible. Under an
explicit averaged-Green inverse hypothesis, the exact self-energy is characterized by the usual
inverse difference

```text
Σ = G₀⁻¹ - Ḡ⁻¹.
```

This bridge is exact and does not identify the averaged Green operator with Born or SCBA
approximation data.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- If `averagedInverse` is a two-sided inverse of the exact averaged Green operator, then a
candidate self-energy satisfies the exact two-sided Dyson relation exactly when it is the difference
between the clean spectral shift and `averagedInverse`.

The nonzero-broadening hypothesis supplies the two-sided inverse of the clean Green operator. -/
theorem averagedGreen_isSelfEnergy_iff_eq_inverse_sub_inverse
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (averagedInverse selfEnergy : H →L[ℂ] H)
    (haveragedLeft :
      averagedInverse * ensemble.averagedGreen side energy broadening = 1)
    (haveragedRight :
      ensemble.averagedGreen side energy broadening * averagedInverse = 1) :
    IsSelfEnergy
        (ensemble.freeGreen side energy broadening)
        (ensemble.averagedGreen side energy broadening)
        selfEnergy ↔
      selfEnergy =
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
            ensemble.baseHamiltonian.1) - averagedInverse := by
  let freeInverse : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      ensemble.baseHamiltonian.1
  have hfreeLeft :
      freeInverse * ensemble.freeGreen side energy broadening = 1 := by
    simpa [freeInverse, FiniteDisorderEnsemble.freeGreen] using
      spectralShift_mul_spectralResolvent side
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
        energy broadening hbroadening
  have hfreeRight :
      ensemble.freeGreen side energy broadening * freeInverse = 1 := by
    simpa [freeInverse, FiniteDisorderEnsemble.freeGreen] using
      spectralResolvent_mul_spectralShift side
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
        energy broadening hbroadening
  have hiff := IsSelfEnergy.iff_eq_inverse_sub_inverse
    (freeGreen := ensemble.freeGreen side energy broadening)
    (dressedGreen := ensemble.averagedGreen side energy broadening)
    (selfEnergy := selfEnergy)
    (freeInverse := freeInverse)
    (dressedInverse := averagedInverse)
    hfreeLeft hfreeRight haveragedLeft haveragedRight
  simpa [freeInverse] using hiff

/-- A supplied two-sided inverse of the exact averaged Green operator produces an exact Dyson
self-energy through the inverse-difference formula. -/
theorem averagedGreen_inverseDifference_isSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (averagedInverse : H →L[ℂ] H)
    (haveragedLeft :
      averagedInverse * ensemble.averagedGreen side energy broadening = 1)
    (haveragedRight :
      ensemble.averagedGreen side energy broadening * averagedInverse = 1) :
    IsSelfEnergy
      (ensemble.freeGreen side energy broadening)
      (ensemble.averagedGreen side energy broadening)
      ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
          ensemble.baseHamiltonian.1) - averagedInverse) := by
  apply (ensemble.averagedGreen_isSelfEnergy_iff_eq_inverse_sub_inverse
    side energy broadening hbroadening averagedInverse
    ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
        ensemble.baseHamiltonian.1) - averagedInverse)
    haveragedLeft haveragedRight).2
  rfl

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
