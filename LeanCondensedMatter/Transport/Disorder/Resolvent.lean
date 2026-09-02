import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Exact finite-disorder Green operators and Dyson identities

This module owns exact Green-operator data for a finite disorder ensemble before any moment
assumption or weak-disorder closure is imposed. The analytic core is parameterized by an arbitrary
signed imaginary regulator

```text
z(E, γ) = E + iγ.
```

Physical retarded/advanced branches specialize this core through `γ = side.sign * η`. Exact Dyson
identities are stated only for the arbitrary-regulator core; consumers specialize the regulator
locally when physical branch semantics are needed.

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

/-- Exact clean Green operator at an arbitrary signed imaginary regulator. -/
noncomputable def freeGreenOfRegulator
    (energy regulator : ℝ) : H →L[ℂ] H :=
  resolvent ensemble.baseHamiltonian.1 (spectralParameterOfRegulator energy regulator)

/-- Exact Green operator of one disordered configuration at an arbitrary signed regulator. -/
noncomputable def configurationGreenOfRegulator
    (energy regulator : ℝ) (ω : Ω) : H →L[ℂ] H :=
  resolvent (ensemble.configurationHamiltonian ω).1
    (spectralParameterOfRegulator energy regulator)

/-- Exact finite disorder average of the complete configuration Green operator at an arbitrary
signed regulator. No Born or self-consistent closure is imposed. -/
noncomputable def averagedGreenOfRegulator
    (energy regulator : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω => ensemble.configurationGreenOfRegulator energy regulator ω)

/-- Adjointing the exact finite disorder-averaged Green operator reverses the signed regulator. -/
theorem star_averagedGreenOfRegulator
    (energy regulator : ℝ) :
    star (ensemble.averagedGreenOfRegulator energy regulator) =
      ensemble.averagedGreenOfRegulator energy (-regulator) := by
  unfold averagedGreenOfRegulator
  rw [← ensemble.operatorAverage_star]
  apply congrArg ensemble.operatorAverage
  funext ω
  unfold configurationGreenOfRegulator
  exact star_resolvent_spectralParameterOfRegulator
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy regulator

/-- Exact left-oriented configuration Dyson identity at an arbitrary nonzero signed regulator,
`Gω = G₀ + G₀ Vω Gω`. -/
theorem configurationGreenOfRegulator_eq_free_add_dyson_left
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω) :
    ensemble.configurationGreenOfRegulator energy regulator ω =
      ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreenOfRegulator energy regulator ω := by
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree : ensemble.freeGreenOfRegulator energy regulator * shift₀ = 1 := by
    simpa [freeGreenOfRegulator, shift₀] using
      resolvent_spectralParameterOfRegulator_mul_spectralShift
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  have hconfiguration :
      shiftω * ensemble.configurationGreenOfRegulator energy regulator ω = 1 := by
    simpa [configurationGreenOfRegulator, shiftω] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  calc
    ensemble.configurationGreenOfRegulator energy regulator ω =
        ensemble.freeGreenOfRegulator energy regulator * shift₀ *
          ensemble.configurationGreenOfRegulator energy regulator ω := by
      rw [hfree]
      simp
    _ = ensemble.freeGreenOfRegulator energy regulator *
          (shiftω + (ensemble.impurityPotential ω).1) *
            ensemble.configurationGreenOfRegulator energy regulator ω := by
      rw [hshift]
    _ = ensemble.freeGreenOfRegulator energy regulator *
          (shiftω * ensemble.configurationGreenOfRegulator energy regulator ω) +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreenOfRegulator energy regulator ω := by
      noncomm_ring
    _ = ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreenOfRegulator energy regulator ω := by
      rw [hconfiguration]
      simp

/-- Exact right-oriented configuration Dyson identity at an arbitrary nonzero signed regulator,
`Gω = G₀ + Gω Vω G₀`. -/
theorem configurationGreenOfRegulator_eq_free_add_dyson_right
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω) :
    ensemble.configurationGreenOfRegulator energy regulator ω =
      ensemble.freeGreenOfRegulator energy regulator +
        ensemble.configurationGreenOfRegulator energy regulator ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator := by
  let shift₀ : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      ensemble.baseHamiltonian.1
  let shiftω : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      (ensemble.configurationHamiltonian ω).1
  have hshift : shift₀ = shiftω + (ensemble.impurityPotential ω).1 := by
    dsimp [shift₀, shiftω, FiniteDisorderEnsemble.configurationHamiltonian]
    noncomm_ring
  have hfree : shift₀ * ensemble.freeGreenOfRegulator energy regulator = 1 := by
    simpa [freeGreenOfRegulator, shift₀] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  have hconfiguration :
      ensemble.configurationGreenOfRegulator energy regulator ω * shiftω = 1 := by
    simpa [configurationGreenOfRegulator, shiftω] using
      resolvent_spectralParameterOfRegulator_mul_spectralShift
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  calc
    ensemble.configurationGreenOfRegulator energy regulator ω =
        ensemble.configurationGreenOfRegulator energy regulator ω * shift₀ *
          ensemble.freeGreenOfRegulator energy regulator := by
      calc
        ensemble.configurationGreenOfRegulator energy regulator ω =
            ensemble.configurationGreenOfRegulator energy regulator ω * 1 := by simp
        _ = ensemble.configurationGreenOfRegulator energy regulator ω *
            (shift₀ * ensemble.freeGreenOfRegulator energy regulator) := by rw [hfree]
        _ = _ := by rw [mul_assoc]
    _ = ensemble.configurationGreenOfRegulator energy regulator ω *
          (shiftω + (ensemble.impurityPotential ω).1) *
            ensemble.freeGreenOfRegulator energy regulator := by
      rw [hshift]
    _ = (ensemble.configurationGreenOfRegulator energy regulator ω * shiftω) *
          ensemble.freeGreenOfRegulator energy regulator +
        ensemble.configurationGreenOfRegulator energy regulator ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator := by
      noncomm_ring
    _ = ensemble.freeGreenOfRegulator energy regulator +
        ensemble.configurationGreenOfRegulator energy regulator ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator := by
      rw [hconfiguration]
      simp

/-- Exact left-oriented second-order Dyson expansion at an arbitrary nonzero signed regulator. -/
theorem configurationGreenOfRegulator_eq_secondOrder_add_exactRemainder_left
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω) :
    ensemble.configurationGreenOfRegulator energy regulator ω =
      ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator *
              (ensemble.impurityPotential ω).1 *
                ensemble.configurationGreenOfRegulator energy regulator ω := by
  have hdyson := configurationGreenOfRegulator_eq_free_add_dyson_left
    ensemble energy regulator hregulator ω
  calc
    ensemble.configurationGreenOfRegulator energy regulator ω =
        ensemble.freeGreenOfRegulator energy regulator +
          ensemble.freeGreenOfRegulator energy regulator *
            (ensemble.impurityPotential ω).1 *
              ensemble.configurationGreenOfRegulator energy regulator ω := hdyson
    _ = ensemble.freeGreenOfRegulator energy regulator +
          ensemble.freeGreenOfRegulator energy regulator *
            (ensemble.impurityPotential ω).1 *
              (ensemble.freeGreenOfRegulator energy regulator +
                ensemble.freeGreenOfRegulator energy regulator *
                  (ensemble.impurityPotential ω).1 *
                    ensemble.configurationGreenOfRegulator energy regulator ω) := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeGreenOfRegulator energy regulator +
            ensemble.freeGreenOfRegulator energy regulator *
              (ensemble.impurityPotential ω).1 * green)
        hdyson
    _ = _ := by
      noncomm_ring

/-- Exact right-oriented second-order Dyson expansion at an arbitrary nonzero signed regulator. -/
theorem configurationGreenOfRegulator_eq_secondOrder_add_exactRemainder_right
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω) :
    ensemble.configurationGreenOfRegulator energy regulator ω =
      ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator +
        ensemble.configurationGreenOfRegulator energy regulator ω *
          (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreenOfRegulator energy regulator := by
  have hdyson := configurationGreenOfRegulator_eq_free_add_dyson_right
    ensemble energy regulator hregulator ω
  calc
    ensemble.configurationGreenOfRegulator energy regulator ω =
        ensemble.freeGreenOfRegulator energy regulator +
          ensemble.configurationGreenOfRegulator energy regulator ω *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreenOfRegulator energy regulator := hdyson
    _ = ensemble.freeGreenOfRegulator energy regulator +
          (ensemble.freeGreenOfRegulator energy regulator +
            ensemble.configurationGreenOfRegulator energy regulator ω *
              (ensemble.impurityPotential ω).1 *
                ensemble.freeGreenOfRegulator energy regulator) *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreenOfRegulator energy regulator := by
      exact congrArg
        (fun green : H →L[ℂ] H =>
          ensemble.freeGreenOfRegulator energy regulator + green *
            (ensemble.impurityPotential ω).1 *
              ensemble.freeGreenOfRegulator energy regulator)
        hdyson
    _ = _ := by
      noncomm_ring

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
