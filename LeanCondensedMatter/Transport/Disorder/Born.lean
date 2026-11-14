import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Disorder.Resolvent
import Mathlib.Tactic.NoncommRing

set_option linter.style.header false

/-!
# Finite-disorder Born self-energy

This module owns the conventional first-Born self-energy for a finite disorder ensemble. The
analytic core is the exact finite second-moment action evaluated on the clean Green operator at an
arbitrary signed regulator `γ`; physical retarded/advanced consumers specialize the regulator
locally through `γ = side.regulator η`.

No equality with the exact disorder-averaged self-energy or self-consistency is asserted here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- First-Born self-energy at an arbitrary signed regulator: the exact finite second moment applied
to the corresponding clean Green operator. -/
noncomputable def bornSelfEnergyOfRegulator
    (energy regulator : ℝ) : H →L[ℂ] H :=
  ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy regulator)

/-- Adjointing the first-Born self-energy reverses the signed regulator. -/
theorem star_bornSelfEnergyOfRegulator
    (energy regulator : ℝ) :
    star (ensemble.bornSelfEnergyOfRegulator energy regulator) =
      ensemble.bornSelfEnergyOfRegulator energy (-regulator) := by
  unfold bornSelfEnergyOfRegulator
  calc
    star (ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy regulator)) =
        ensemble.exactSecondMoment (star (ensemble.freeGreenOfRegulator energy regulator)) :=
      (ensemble.exactSecondMoment_star
        (ensemble.freeGreenOfRegulator energy regulator)).symm
    _ = ensemble.exactSecondMoment (ensemble.freeGreenOfRegulator energy (-regulator)) := by
      apply congrArg ensemble.exactSecondMoment
      unfold freeGreenOfRegulator
      exact star_resolvent_spectralParameterOfRegulator
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator

/-- Exact finite-ensemble third-order remainder of the centered Born expansion.

For any nonzero signed regulator, the averaged resolvent equals the clean Green operator
plus the first nonzero Born contribution `G₀ C₂(G₀) G₀` and a *specified* remainder
containing three impurity potentials and one exact configuration Green operator.

This is an identity, not an asymptotic expansion or an error estimate. A norm bound
requires additional quantitative control of the impurity potentials and resolvents. -/
theorem averagedGreenOfRegulator_eq_born_add_exactRemainder_of_centered
    (energy regulator : ℝ) (hregulator : regulator ≠ 0)
    (hcentered : ensemble.IsCentered) :
    ensemble.averagedGreenOfRegulator energy regulator =
      ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          ensemble.bornSelfEnergyOfRegulator energy regulator *
            ensemble.freeGreenOfRegulator energy regulator +
        ensemble.average (fun ω =>
          ensemble.freeGreenOfRegulator energy regulator *
            (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator *
            (ensemble.impurityPotential ω).1 *
            ensemble.configurationGreenOfRegulator energy regulator ω *
            (ensemble.impurityPotential ω).1 *
            ensemble.freeGreenOfRegulator energy regulator) := by
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let V : Ω → H →L[ℂ] H := fun ω => (ensemble.impurityPotential ω).1
  let G : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energy regulator ω
  let remainder : Ω → H →L[ℂ] H :=
    fun ω => G₀ * V ω * G₀ * V ω * G ω * V ω * G₀
  have hpoint (ω : Ω) :
      G ω = G₀ + G₀ * V ω * G₀ +
        G₀ * (V ω * G₀ * V ω) * G₀ + remainder ω := by
    have h2 := ensemble.configurationGreenOfRegulator_eq_secondOrder_add_exactRemainder_left
      energy regulator hregulator ω
    have hr := ensemble.configurationGreenOfRegulator_eq_free_add_dyson_right
      energy regulator hregulator ω
    change G ω = G₀ + G₀ * V ω * G₀ + G₀ * V ω * G₀ * V ω * G ω at h2
    change G ω = G₀ + G ω * V ω * G₀ at hr
    calc
      G ω = G₀ + G₀ * V ω * G₀ + G₀ * V ω * G₀ * V ω * G ω := h2
      _ = G₀ + G₀ * V ω * G₀ +
          G₀ * V ω * G₀ * V ω * (G₀ + G ω * V ω * G₀) := by nth_rw 1 [hr]
      _ = G₀ + G₀ * V ω * G₀ +
          G₀ * (V ω * G₀ * V ω) * G₀ + remainder ω := by
        dsimp only [remainder]
        noncomm_ring
  have hmean : ensemble.average V = 0 := by
    exact hcentered
  have hfactor (term : Ω → H →L[ℂ] H) :
      ensemble.average (fun ω => G₀ * term ω * G₀) =
        G₀ * ensemble.average term * G₀ := by
    simpa using
      (ensemble.map_average
        ((ContinuousLinearMap.mulLeftRight ℂ (H →L[ℂ] H)) G₀ G₀).toLinearMap
        term).symm
  have hlinear : ensemble.average (fun ω => G₀ * V ω * G₀) = 0 := by
    rw [hfactor V, hmean]
    simp
  have hborn :
      ensemble.average (fun ω => V ω * G₀ * V ω) =
        ensemble.bornSelfEnergyOfRegulator energy regulator := by
    simpa only [G₀, V, bornSelfEnergyOfRegulator] using
      (ensemble.exactSecondMoment_eq_average
        (ensemble.freeGreenOfRegulator energy regulator)).symm
  have haverage :
      ensemble.average G = G₀ +
        G₀ * ensemble.bornSelfEnergyOfRegulator energy regulator * G₀ +
        ensemble.average remainder := by
    calc
      ensemble.average G =
          ensemble.average (fun ω =>
            G₀ + G₀ * V ω * G₀ +
              G₀ * (V ω * G₀ * V ω) * G₀ + remainder ω) := by
        apply congrArg ensemble.average
        funext ω
        exact hpoint ω
      _ = G₀ + G₀ * ensemble.bornSelfEnergyOfRegulator energy regulator * G₀ +
          ensemble.average remainder := by
        change ensemble.average
          ((fun _ : Ω => G₀) + (fun ω => G₀ * V ω * G₀) +
            (fun ω => G₀ * (V ω * G₀ * V ω) * G₀) + remainder) = _
        rw [map_add, map_add, map_add, ensemble.average_const, hlinear,
          hfactor (fun ω => V ω * G₀ * V ω), hborn]
        simp
  exact haverage

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
