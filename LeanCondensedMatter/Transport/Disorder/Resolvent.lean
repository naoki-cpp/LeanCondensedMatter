import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Exact finite-disorder resolvents and Dyson identities

This module owns exact resolvent data for a finite disorder ensemble before any moment assumption or
weak-disorder closure is imposed.

For the clean Hamiltonian `H₀` and each exact configuration Hamiltonian `Hω = H₀ + Vω`, it defines
side-indexed clean and configuration Green operators together with their exact finite disorder
average. Conventional retarded/advanced specializations remain public, and the averaged advanced
Green operator is derived by adjunction from the averaged retarded one. The module also proves
side-indexed left- and right-oriented first- and second-order configuration-wise Dyson identities
with the complete configuration Green operator retained in the remainder.

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

/-- Exact retarded Green operator of one disordered configuration. -/
noncomputable def configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  ensemble.configurationGreen .retarded energy broadening ω

/-- Exact finite disorder-averaged retarded Green operator. -/
noncomputable def averagedRetardedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.averagedGreen .retarded energy broadening

/-- Exact clean advanced Green operator. -/
noncomputable def freeAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.freeGreen .advanced energy broadening

/-- Exact advanced Green operator of one disordered configuration. -/
noncomputable def configurationAdvancedGreen
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  ensemble.configurationGreen .advanced energy broadening ω

/-- Exact finite disorder-averaged advanced Green operator. -/
noncomputable def averagedAdvancedGreen
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.averagedGreen .advanced energy broadening

@[simp]
theorem freeGreen_retarded
    (energy broadening : ℝ) :
    ensemble.freeGreen .retarded energy broadening =
      ensemble.freeRetardedGreen energy broadening :=
  rfl

@[simp]
theorem freeGreen_advanced
    (energy broadening : ℝ) :
    ensemble.freeGreen .advanced energy broadening =
      ensemble.freeAdvancedGreen energy broadening :=
  rfl

@[simp]
theorem configurationGreen_retarded
    (energy broadening : ℝ) (ω : Ω) :
    ensemble.configurationGreen .retarded energy broadening ω =
      ensemble.configurationRetardedGreen energy broadening ω :=
  rfl

@[simp]
theorem configurationGreen_advanced
    (energy broadening : ℝ) (ω : Ω) :
    ensemble.configurationGreen .advanced energy broadening ω =
      ensemble.configurationAdvancedGreen energy broadening ω :=
  rfl

@[simp]
theorem averagedGreen_retarded
    (energy broadening : ℝ) :
    ensemble.averagedGreen .retarded energy broadening =
      ensemble.averagedRetardedGreen energy broadening :=
  rfl

@[simp]
theorem averagedGreen_advanced
    (energy broadening : ℝ) :
    ensemble.averagedGreen .advanced energy broadening =
      ensemble.averagedAdvancedGreen energy broadening :=
  rfl

/-- The clean advanced Green operator is the adjoint of the clean retarded Green operator. -/
theorem star_freeRetardedGreen
    (energy broadening : ℝ) :
    star (ensemble.freeRetardedGreen energy broadening) =
      ensemble.freeAdvancedGreen energy broadening := by
  unfold freeRetardedGreen freeAdvancedGreen freeGreen
  rw [spectralResolvent_retarded, spectralResolvent_advanced]
  exact star_retardedResolvent
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy broadening

/-- The configuration advanced Green operator is the adjoint of the corresponding retarded Green
operator. -/
theorem star_configurationRetardedGreen
    (energy broadening : ℝ) (ω : Ω) :
    star (ensemble.configurationRetardedGreen energy broadening ω) =
      ensemble.configurationAdvancedGreen energy broadening ω := by
  unfold configurationRetardedGreen configurationAdvancedGreen configurationGreen
  rw [spectralResolvent_retarded, spectralResolvent_advanced]
  exact star_retardedResolvent
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy broadening

/-- The exact finite disorder-averaged advanced Green operator is the adjoint of the exact averaged
retarded Green operator. -/
theorem star_averagedRetardedGreen
    (energy broadening : ℝ) :
    star (ensemble.averagedRetardedGreen energy broadening) =
      ensemble.averagedAdvancedGreen energy broadening := by
  unfold averagedRetardedGreen averagedAdvancedGreen averagedGreen
  rw [← ensemble.operatorAverage_star]
  apply congrArg ensemble.operatorAverage
  funext ω
  rw [ensemble.configurationGreen_retarded, ensemble.configurationGreen_advanced,
    ensemble.star_configurationRetardedGreen]

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

/-- Exact first retarded resolvent identity
`Gωᴿ = G₀ᴿ + G₀ᴿ Vω Gωᴿ` at positive broadening. -/
theorem configurationRetardedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedGreen energy broadening ω =
      ensemble.freeRetardedGreen energy broadening +
        ensemble.freeRetardedGreen energy broadening *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationRetardedGreen energy broadening ω := by
  simpa only [configurationGreen_retarded, freeGreen_retarded] using
    configurationGreen_eq_free_add_dyson_left
      ensemble .retarded energy broadening (ne_of_gt hbroadening) ω

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
  simpa only [configurationGreen_retarded, freeGreen_retarded] using
    configurationGreen_eq_secondOrder_add_exactRemainder_left
      ensemble .retarded energy broadening (ne_of_gt hbroadening) ω

/-- Exact right-oriented advanced resolvent identity
`Gωᴬ = G₀ᴬ + Gωᴬ Vω G₀ᴬ` at positive broadening. -/
theorem configurationAdvancedGreen_eq_free_add_dyson
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationAdvancedGreen energy broadening ω =
      ensemble.freeAdvancedGreen energy broadening +
        ensemble.configurationAdvancedGreen energy broadening ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeAdvancedGreen energy broadening := by
  simpa only [configurationGreen_advanced, freeGreen_advanced] using
    configurationGreen_eq_free_add_dyson_right
      ensemble .advanced energy broadening (ne_of_gt hbroadening) ω

/-- Exact second-order advanced Dyson expansion. It is the right-oriented advanced specialization
of the canonical side-indexed expansion, with the complete configuration Green operator retained. -/
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
  simpa only [configurationGreen_advanced, freeGreen_advanced] using
    configurationGreen_eq_secondOrder_add_exactRemainder_right
      ensemble .advanced energy broadening (ne_of_gt hbroadening) ω

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
