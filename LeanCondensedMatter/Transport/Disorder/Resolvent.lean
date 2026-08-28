import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Exact finite-disorder resolvents and Dyson identities

This module owns configuration-wise resolvent identities for an exact finite disorder ensemble,
before any moment assumption or weak-disorder closure is imposed.

For the clean Hamiltonian `H₀` and each exact configuration Hamiltonian `Hω = H₀ + Vω`, it defines
a side-indexed Green-operator core together with conventional retarded/advanced specializations, and
proves the first and second-order Dyson identities with the complete configuration Green operator
retained in the remainder. The advanced identities are derived from the retarded identities by
adjunction.

No centering, covariance, Born approximation, closure hypothesis, self-consistency, disorder
average identification, trace-per-volume construction, or thermodynamic limit is introduced here.
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

/-- Exact clean retarded Green operator. -/
noncomputable def freeRetardedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  retardedResolvent ensemble.baseHamiltonian.1 energy broadening

/-- Exact retarded Green operator of one disordered configuration. -/
noncomputable def configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening

/-- Exact clean advanced Green operator. -/
noncomputable def freeAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  advancedResolvent ensemble.baseHamiltonian.1 energy broadening

/-- Exact advanced Green operator of one disordered configuration. -/
noncomputable def configurationAdvancedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  advancedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening

@[simp]
theorem freeGreen_retarded
    (energy broadening : ℝ) :
    ensemble.freeGreen .retarded energy broadening =
      ensemble.freeRetardedGreen energy broadening := by
  unfold freeGreen freeRetardedGreen
  rw [spectralResolvent_retarded]

@[simp]
theorem freeGreen_advanced
    (energy broadening : ℝ) :
    ensemble.freeGreen .advanced energy broadening =
      ensemble.freeAdvancedGreen energy broadening := by
  unfold freeGreen freeAdvancedGreen
  rw [spectralResolvent_advanced]

@[simp]
theorem configurationGreen_retarded
    (energy broadening : ℝ) (ω : Ω) :
    ensemble.configurationGreen .retarded energy broadening ω =
      ensemble.configurationRetardedGreen energy broadening ω := by
  unfold configurationGreen configurationRetardedGreen
  rw [spectralResolvent_retarded]

@[simp]
theorem configurationGreen_advanced
    (energy broadening : ℝ) (ω : Ω) :
    ensemble.configurationGreen .advanced energy broadening ω =
      ensemble.configurationAdvancedGreen energy broadening ω := by
  unfold configurationGreen configurationAdvancedGreen
  rw [spectralResolvent_advanced]

/-- The clean advanced Green operator is the adjoint of the clean retarded Green operator. -/
theorem star_freeRetardedGreen
    (energy broadening : ℝ) :
    star (ensemble.freeRetardedGreen energy broadening) =
      ensemble.freeAdvancedGreen energy broadening := by
  unfold freeRetardedGreen freeAdvancedGreen
  exact star_retardedResolvent
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy broadening

/-- The configuration advanced Green operator is the adjoint of the corresponding retarded Green
operator. -/
theorem star_configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) :
    star (ensemble.configurationRetardedGreen energy broadening ω) =
      ensemble.configurationAdvancedGreen energy broadening ω := by
  unfold configurationRetardedGreen configurationAdvancedGreen
  exact star_retardedResolvent
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy broadening

/-- Exact first retarded resolvent identity
`Gωᴿ = G₀ᴿ + G₀ᴿ Vω Gωᴿ` at positive broadening. -/
theorem configurationRetardedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedGreen energy broadening ω =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationRetardedGreen energy broadening ω := by
  unfold configurationRetardedGreen freeRetardedGreen
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree := resolvent_mul_retardedShift
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
    energy broadening hbroadening
  have hconfiguration := retardedShift_mul_resolvent
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2
    energy broadening hbroadening
  change retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening = _
  calc
    retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening =
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening * shift₀ *
          retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hfree]
      simp
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (shiftω + (ensemble.impurityPotential ω).1) *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hshift]
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (shiftω * retardedResolvent
            (ensemble.configurationHamiltonian ω).1 energy broadening) +
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      noncomm_ring
    _ = retardedResolvent ensemble.baseHamiltonian.1 energy broadening +
        retardedResolvent ensemble.baseHamiltonian.1 energy broadening *
          (ensemble.impurityPotential ω).1 *
            retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening := by
      rw [hconfiguration]
      simp

/-- Exact second-order retarded Dyson expansion with the complete configuration Green operator
retained in the remainder. This is an identity, not a weak-scattering approximation. -/
theorem configurationRetardedGreen_eq_secondOrder_add_exactRemainder
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedGreen energy broadening ω =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationRetardedGreen energy broadening ω := by
  have hdyson := configurationRetardedGreen_eq_free_add_dyson
    ensemble energy broadening hbroadening ω
  calc
    ensemble.configurationRetardedGreen energy broadening ω =
        ensemble.freeRetardedGreen energy broadening +
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              ensemble.configurationRetardedGreen energy broadening ω := hdyson
    _ = ensemble.freeRetardedGreen energy broadening +
          ensemble.freeRetardedGreen energy broadening *
            (ensemble.impurityPotential ω).1 *
              (ensemble.freeRetardedGreen energy broadening +
                ensemble.freeRetardedGreen energy broadening *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.configurationRetardedGreen energy broadening ω) := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeRetardedGreen energy broadening +
            ensemble.freeRetardedGreen energy broadening *
              (ensemble.impurityPotential ω).1 * green)
        hdyson
    _ = _ := by
      noncomm_ring

/-- Exact right-oriented advanced resolvent identity
`Gωᴬ = G₀ᴬ + Gωᴬ Vω G₀ᴬ` at positive broadening. -/
theorem configurationAdvancedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationAdvancedGreen energy broadening ω =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening := by
  have hretarded := congrArg star
    (configurationRetardedGreen_eq_free_add_dyson
      ensemble energy broadening hbroadening ω)
  simpa [star_add, star_mul, star_configurationRetardedGreen,
    star_freeRetardedGreen, (ensemble.impurityPotential ω).2.star_eq, mul_assoc] using hretarded

/-- Exact second-order advanced Dyson expansion. It is the adjoint of the exact retarded expansion,
so no independent advanced weak-scattering assumption is introduced. -/
theorem configurationAdvancedGreen_eq_secondOrder_add_exactRemainder
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationAdvancedGreen energy broadening ω =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.freeAdvancedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeAdvancedGreen energy broadening := by
  have hretarded := congrArg star
    (configurationRetardedGreen_eq_secondOrder_add_exactRemainder
      ensemble energy broadening hbroadening ω)
  simpa [star_add, star_mul, star_configurationRetardedGreen,
    star_freeRetardedGreen, (ensemble.impurityPotential ω).2.star_eq, mul_assoc] using hretarded

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
