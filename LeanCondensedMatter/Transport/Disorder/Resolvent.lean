import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Exact finite-disorder resolvents and Dyson identities

This module owns exact resolvent data for a finite disorder ensemble before any moment assumption or
weak-disorder closure is imposed.

For the clean Hamiltonian `H₀` and each exact configuration Hamiltonian `Hω = H₀ + Vω`, it defines
side-indexed clean and configuration Green operators together with their exact finite disorder
average. Clean and averaged retarded/advanced specializations remain public, while adjunction is
stated once for an arbitrary spectral side and exchanges it with the opposite side. The module also
proves side-indexed left- and right-oriented first- and second-order configuration-wise Dyson
identities with the complete configuration Green operator retained in the remainder.

No centering, covariance, Born approximation, closure hypothesis, self-consistency, effective
self-energy identification, trace-per-volume construction, or thermodynamic limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Exact clean Green operator on either spectral side. -/
noncomputable def freeGreen
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  spectralResolvent side ensemble.baseHamiltonian.1 energy broadening

/-- Exact Green operator of one disordered configuration on either spectral side. -/
noncomputable def configurationGreen
    (side : SpectralSide) (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  spectralResolvent side (ensemble.configurationHamiltonian ω).1 energy broadening

/-- Exact finite disorder average of the complete configuration Green operator on either spectral
side, `Ḡˢ = E[Gωˢ]`. No Born or self-consistent closure is imposed. -/
noncomputable def averagedGreen
    (side : SpectralSide) (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω => ensemble.configurationGreen side energy broadening ω)

/-- Exact clean retarded Green operator. -/
noncomputable def freeRetardedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.freeGreen .retarded energy broadening

/-- Exact finite disorder-averaged retarded Green operator. -/
noncomputable def averagedRetardedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.averagedGreen .retarded energy broadening

/-- Exact clean advanced Green operator. -/
noncomputable def freeAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.freeGreen .advanced energy broadening

/-- Exact finite disorder-averaged advanced Green operator. -/
noncomputable def averagedAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.averagedGreen .advanced energy broadening

/-- Adjointing the exact finite disorder-averaged Green operator exchanges the spectral side. -/
theorem star_averagedGreen
    (side : SpectralSide) (energy broadening : ℝ) :
    star (ensemble.averagedGreen side energy broadening) =
      ensemble.averagedGreen side.opposite energy broadening := by
  unfold averagedGreen
  rw [← ensemble.operatorAverage_star]
  apply congrArg ensemble.operatorAverage
  funext ω
  unfold configurationGreen
  exact star_spectralResolvent side
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy broadening

/-- Exact left-oriented configuration Dyson identity on either spectral side,
`Gωˢ = G₀ˢ + G₀ˢ Vω Gωˢ`, for nonzero broadening. -/
theorem configurationGreen_eq_free_add_dyson_left
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (ω : Ω) :
    ensemble.configurationGreen side energy broadening ω =
      ensemble.freeGreen side energy broadening +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreen side energy broadening ω := by
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree : ensemble.freeGreen side energy broadening * shift₀ = 1 := by
    simpa [freeGreen, shift₀] using
      spectralResolvent_mul_spectralShift side
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
        energy broadening hbroadening
  have hconfiguration :
      shiftω * ensemble.configurationGreen side energy broadening ω = 1 := by
    simpa [configurationGreen, shiftω] using
      spectralShift_mul_spectralResolvent side
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2
        energy broadening hbroadening
  calc
    ensemble.configurationGreen side energy broadening ω =
        ensemble.freeGreen side energy broadening * shift₀ *
          ensemble.configurationGreen side energy broadening ω := by
      rw [hfree]
      simp
    _ = ensemble.freeGreen side energy broadening *
          (shiftω + (ensemble.impurityPotential ω).1) *
            ensemble.configurationGreen side energy broadening ω := by
      rw [hshift]
    _ = ensemble.freeGreen side energy broadening *
          (shiftω * ensemble.configurationGreen side energy broadening ω) +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreen side energy broadening ω := by
      noncomm_ring
    _ = ensemble.freeGreen side energy broadening +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreen side energy broadening ω := by
      rw [hconfiguration]
      simp

/-- Exact right-oriented configuration Dyson identity on either spectral side,
`Gωˢ = G₀ˢ + Gωˢ Vω G₀ˢ`, for nonzero broadening. -/
theorem configurationGreen_eq_free_add_dyson_right
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (ω : Ω) :
    ensemble.configurationGreen side energy broadening ω =
      ensemble.freeGreen side energy broadening +
        ensemble.configurationGreen side energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening := by
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree : shift₀ * ensemble.freeGreen side energy broadening = 1 := by
    simpa [freeGreen, shift₀] using
      spectralShift_mul_spectralResolvent side
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
        energy broadening hbroadening
  have hconfiguration :
      ensemble.configurationGreen side energy broadening ω * shiftω = 1 := by
    simpa [configurationGreen, shiftω] using
      spectralResolvent_mul_spectralShift side
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2
        energy broadening hbroadening
  calc
    ensemble.configurationGreen side energy broadening ω =
        ensemble.configurationGreen side energy broadening ω * shift₀ *
          ensemble.freeGreen side energy broadening := by
      calc
        ensemble.configurationGreen side energy broadening ω =
            ensemble.configurationGreen side energy broadening ω * 1 := by simp
        _ = ensemble.configurationGreen side energy broadening ω *
            (shift₀ * ensemble.freeGreen side energy broadening) := by rw [hfree]
        _ = _ := by rw [mul_assoc]
    _ = ensemble.configurationGreen side energy broadening ω *
          (shiftω + (ensemble.impurityPotential ω).1) *
            ensemble.freeGreen side energy broadening := by
      rw [hshift]
    _ = (ensemble.configurationGreen side energy broadening ω * shiftω) *
          ensemble.freeGreen side energy broadening +
        ensemble.configurationGreen side energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening := by
      noncomm_ring
    _ = ensemble.freeGreen side energy broadening +
        ensemble.configurationGreen side energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening := by
      rw [hconfiguration]
      simp

/-- Exact left-oriented second-order Dyson expansion on either spectral side. -/
theorem configurationGreen_eq_secondOrder_add_exactRemainder_left
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (ω : Ω) :
    ensemble.configurationGreen side energy broadening ω =
      ensemble.freeGreen side energy broadening +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationGreen side energy broadening ω := by
  have hdyson := configurationGreen_eq_free_add_dyson_left
    ensemble side energy broadening hbroadening ω
  calc
    ensemble.configurationGreen side energy broadening ω =
        ensemble.freeGreen side energy broadening +
          ensemble.freeGreen side energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.configurationGreen side energy broadening ω := hdyson
    _ = ensemble.freeGreen side energy broadening +
          ensemble.freeGreen side energy broadening *
            (ensemble.impurityPotential ω).1 *
              (ensemble.freeGreen side energy broadening +
                ensemble.freeGreen side energy broadening *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.configurationGreen side energy broadening ω) := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeGreen side energy broadening +
            ensemble.freeGreen side energy broadening *
              (ensemble.impurityPotential ω).1 * green)
        hdyson
    _ = _ := by
      noncomm_ring

/-- Exact right-oriented second-order Dyson expansion on either spectral side. -/
theorem configurationGreen_eq_secondOrder_add_exactRemainder_right
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (ω : Ω) :
    ensemble.configurationGreen side energy broadening ω =
      ensemble.freeGreen side energy broadening +
        ensemble.freeGreen side energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening +
        ensemble.configurationGreen side energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreen side energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen side energy broadening := by
  have hdyson := configurationGreen_eq_free_add_dyson_right
    ensemble side energy broadening hbroadening ω
  calc
    ensemble.configurationGreen side energy broadening ω =
        ensemble.freeGreen side energy broadening +
          ensemble.configurationGreen side energy broadening ω *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreen side energy broadening := hdyson
    _ = ensemble.freeGreen side energy broadening +
          (ensemble.freeGreen side energy broadening +
            ensemble.configurationGreen side energy broadening ω *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreen side energy broadening) *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreen side energy broadening := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeGreen side energy broadening + green *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreen side energy broadening)
        hdyson
    _ = _ := by
      noncomm_ring

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
