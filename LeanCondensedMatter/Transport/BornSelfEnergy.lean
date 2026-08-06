import LeanCondensedMatter.Transport.FiniteDisorder
import LeanCondensedMatter.Transport.Resolvent

set_option linter.style.header false

/-!
# Finite-dimensional weak-scattering Born self-energy

This module separates two statements that are often conflated in informal disorder calculations.
For a finite centered disorder ensemble it first proves an exact iterated resolvent identity with an
explicit remainder. It then defines the Born self-energy and the associated second-order
approximation obtained by replacing the terminal exact configuration resolvent by the clean
resolvent.

The exact theorem is

```text
E[Gω] = G₀ + δGᴮ + Rᴮ,
```

where `δGᴮ = G₀ Σᴮ G₀`, `Σᴮ = E[Vω G₀ Vω]`, and `Rᴮ` is retained explicitly. Thus the Born
approximation is a named truncation, not an exact closed self-energy theorem.

No self-consistent Born approximation, vertex correction, Ward identity, trace-per-volume
construction, or thermodynamic limit is introduced here.
-/

namespace QuantumTheory
namespace Transport

open scoped BigOperators

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [FiniteDimensional ℂ H] [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Finite weighted average of a configuration-dependent bounded operator. -/
noncomputable def operatorAverage (operator : Ω → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ ω, (ensemble.probability ω : ℂ) • operator ω

@[simp]
theorem operatorAverage_zero :
    ensemble.operatorAverage (fun _ => 0) = 0 := by
  simp [operatorAverage]

/-- Normalization makes the operator average of a constant equal to that constant. -/
theorem operatorAverage_const (operator : H →L[ℂ] H) :
    ensemble.operatorAverage (fun _ => operator) = operator := by
  unfold operatorAverage
  rw [← Finset.sum_smul]
  have hprobability :
      ∑ ω, (ensemble.probability ω : ℂ) = 1 := by
    exact_mod_cast ensemble.probability_sum
  rw [hprobability, one_smul]

/-- Finite operator averaging is additive. -/
theorem operatorAverage_add
    (left right : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => left ω + right ω) =
      ensemble.operatorAverage left + ensemble.operatorAverage right := by
  simp [operatorAverage, smul_add, Finset.sum_add_distrib]

/-- A fixed left operator can be pulled through the finite average. -/
theorem operatorAverage_mul_left
    (left : H →L[ℂ] H) (operator : Ω → H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => left * operator ω) =
      left * ensemble.operatorAverage operator := by
  unfold operatorAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [mul_smul_comm]

/-- A fixed right operator can be pulled through the finite average. -/
theorem operatorAverage_mul_right
    (operator : Ω → H →L[ℂ] H) (right : H →L[ℂ] H) :
    ensemble.operatorAverage (fun ω => operator ω * right) =
      ensemble.operatorAverage operator * right := by
  unfold operatorAverage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_mul_assoc]

/-- Explicit centering condition `E[Vω] = 0` for the finite disorder ensemble. -/
def IsCentered : Prop :=
  ensemble.operatorAverage (fun ω => (ensemble.impurityPotential ω).1) = 0

/-- Exact covariance action of the centered impurity ensemble on a bounded operator. This is a
finite second moment; no Gaussian assumption is made. -/
noncomputable def covarianceAction (middle : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    (ensemble.impurityPotential ω).1 * middle * (ensemble.impurityPotential ω).1)

/-- Clean retarded resolvent of the base Hamiltonian. -/
noncomputable def cleanRetardedResolvent
    (energy broadening : ℝ) : H →L[ℂ] H :=
  retardedResolvent ensemble.baseHamiltonian.1 energy broadening

/-- Exact retarded resolvent in one disorder configuration. -/
noncomputable def configurationRetardedResolvent
    (energy broadening : ℝ) (ω : Ω) : H →L[ℂ] H :=
  retardedResolvent (ensemble.configurationHamiltonian ω).1 energy broadening

/-- Exact finite average of the configuration retarded resolvents. -/
noncomputable def averagedRetardedResolvent
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (ensemble.configurationRetardedResolvent energy broadening)

/-- Resolvent perturbation identity for one exact finite disorder configuration. -/
theorem configurationRetardedResolvent_sub_clean
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedResolvent energy broadening ω -
        ensemble.cleanRetardedResolvent energy broadening =
      ensemble.configurationRetardedResolvent energy broadening ω *
        (ensemble.impurityPotential ω).1 *
        ensemble.cleanRetardedResolvent energy broadening := by
  have hconfiguration := retardedSpectralParameter_mem_resolventSet
    (ensemble.configurationHamiltonian ω).1
    (ensemble.configurationHamiltonian ω).2 energy broadening hbroadening
  have hclean := retardedSpectralParameter_mem_resolventSet
    ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy broadening hbroadening
  unfold configurationRetardedResolvent cleanRetardedResolvent
    retardedResolvent resolvent
  calc
    ((algebraMap ℂ (H →L[ℂ] H)
          (retardedSpectralParameter energy broadening) -
        (ensemble.configurationHamiltonian ω).1)⁻¹ -
      (algebraMap ℂ (H →L[ℂ] H)
          (retardedSpectralParameter energy broadening) -
        ensemble.baseHamiltonian.1)⁻¹) =
        (algebraMap ℂ (H →L[ℂ] H)
            (retardedSpectralParameter energy broadening) -
          (ensemble.configurationHamiltonian ω).1)⁻¹ *
          ((algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy broadening) -
            ensemble.baseHamiltonian.1) -
            (algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy broadening) -
            (ensemble.configurationHamiltonian ω).1)) *
          (algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy broadening) -
            ensemble.baseHamiltonian.1)⁻¹ :=
      Ring.inverse_sub_inverse (iff_of_true hconfiguration hclean)
    _ = _ := by
      rw [ensemble.configurationHamiltonian_apply]
      noncomm_ring

/-- First resolvent perturbation identity in additive form. -/
theorem configurationRetardedResolvent_eq_clean_add
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedResolvent energy broadening ω =
      ensemble.cleanRetardedResolvent energy broadening +
        ensemble.configurationRetardedResolvent energy broadening ω *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening := by
  have h := sub_eq_iff_eq_add.mp
    (ensemble.configurationRetardedResolvent_sub_clean
      energy broadening hbroadening ω)
  simpa [add_comm] using h

/-- Exact twice-iterated resolvent identity. The final factor is still the exact configuration
resolvent, so this is not yet a Born approximation. -/
theorem configurationRetardedResolvent_eq_secondOrder
    (energy broadening : ℝ) (hbroadening : 0 < broadening) (ω : Ω) :
    ensemble.configurationRetardedResolvent energy broadening ω =
      ensemble.cleanRetardedResolvent energy broadening +
        ensemble.cleanRetardedResolvent energy broadening *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening +
        ensemble.configurationRetardedResolvent energy broadening ω *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening := by
  calc
    ensemble.configurationRetardedResolvent energy broadening ω =
        ensemble.cleanRetardedResolvent energy broadening +
          ensemble.configurationRetardedResolvent energy broadening ω *
            (ensemble.impurityPotential ω).1 *
            ensemble.cleanRetardedResolvent energy broadening :=
      ensemble.configurationRetardedResolvent_eq_clean_add
        energy broadening hbroadening ω
    _ = ensemble.cleanRetardedResolvent energy broadening +
        (ensemble.cleanRetardedResolvent energy broadening +
          ensemble.configurationRetardedResolvent energy broadening ω *
            (ensemble.impurityPotential ω).1 *
            ensemble.cleanRetardedResolvent energy broadening) *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening := by
      rw [ensemble.configurationRetardedResolvent_eq_clean_add
        energy broadening hbroadening ω]
    _ = _ := by
      noncomm_ring

/-- Exact terminal second-order contribution after centering removes the first-order average. -/
noncomputable def exactSecondOrderRetardedContribution
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    ensemble.configurationRetardedResolvent energy broadening ω *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening)

/-- The Born self-energy `Σᴮ = E[Vω G₀ Vω]`, i.e. the covariance action evaluated on the clean
resolvent. This is the defined second-order approximation kernel, not an exact closed self-energy. -/
noncomputable def bornRetardedSelfEnergy
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.covarianceAction (ensemble.cleanRetardedResolvent energy broadening)

/-- The second-order Born correction to the averaged retarded resolvent. -/
noncomputable def bornRetardedCorrection
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    ensemble.cleanRetardedResolvent energy broadening *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening)

/-- Named Born approximation `G₀ + δGᴮ` to the averaged retarded resolvent. -/
noncomputable def bornAveragedRetardedResolventApproximation
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.cleanRetardedResolvent energy broadening +
    ensemble.bornRetardedCorrection energy broadening

/-- Explicit remainder discarded by the second-order Born approximation. -/
noncomputable def bornRetardedRemainder
    (energy broadening : ℝ) : H →L[ℂ] H :=
  ensemble.operatorAverage (fun ω =>
    (ensemble.configurationRetardedResolvent energy broadening ω -
        ensemble.cleanRetardedResolvent energy broadening) *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening *
      (ensemble.impurityPotential ω).1 *
      ensemble.cleanRetardedResolvent energy broadening)

/-- The Born correction factors as `G₀ Σᴮ G₀`. -/
theorem bornRetardedCorrection_eq_clean_mul_selfEnergy_mul_clean
    (energy broadening : ℝ) :
    ensemble.bornRetardedCorrection energy broadening =
      ensemble.cleanRetardedResolvent energy broadening *
        ensemble.bornRetardedSelfEnergy energy broadening *
        ensemble.cleanRetardedResolvent energy broadening := by
  unfold bornRetardedCorrection bornRetardedSelfEnergy covarianceAction
  rw [← ensemble.operatorAverage_mul_left]
  rw [← ensemble.operatorAverage_mul_right]
  apply congrArg ensemble.operatorAverage
  funext ω
  noncomm_ring

/-- Centering removes the exact first-order averaged resolvent contribution. -/
theorem operatorAverage_clean_mul_impurity_mul_clean_eq_zero
    (hcentered : ensemble.IsCentered) (energy broadening : ℝ) :
    ensemble.operatorAverage (fun ω =>
      ensemble.cleanRetardedResolvent energy broadening *
        (ensemble.impurityPotential ω).1 *
        ensemble.cleanRetardedResolvent energy broadening) = 0 := by
  calc
    ensemble.operatorAverage (fun ω =>
        ensemble.cleanRetardedResolvent energy broadening *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening) =
        ensemble.operatorAverage (fun ω =>
          ensemble.cleanRetardedResolvent energy broadening *
            (ensemble.impurityPotential ω).1) *
          ensemble.cleanRetardedResolvent energy broadening :=
      ensemble.operatorAverage_mul_right _ _
    _ = (ensemble.cleanRetardedResolvent energy broadening *
          ensemble.operatorAverage (fun ω =>
            (ensemble.impurityPotential ω).1)) *
          ensemble.cleanRetardedResolvent energy broadening := by
      rw [ensemble.operatorAverage_mul_left]
    _ = 0 := by
      rw [hcentered]
      simp

/-- Exact centered average after two resolvent iterations. -/
theorem averagedRetardedResolvent_eq_clean_add_exactSecondOrder
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedRetardedResolvent energy broadening =
      ensemble.cleanRetardedResolvent energy broadening +
        ensemble.exactSecondOrderRetardedContribution energy broadening := by
  have hfunctions :
      ensemble.configurationRetardedResolvent energy broadening =
        (fun ω =>
          ensemble.cleanRetardedResolvent energy broadening +
            ensemble.cleanRetardedResolvent energy broadening *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening +
            ensemble.configurationRetardedResolvent energy broadening ω *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening) := by
    funext ω
    exact ensemble.configurationRetardedResolvent_eq_secondOrder
      energy broadening hbroadening ω
  unfold averagedRetardedResolvent exactSecondOrderRetardedContribution
  rw [hfunctions]
  rw [ensemble.operatorAverage_add, ensemble.operatorAverage_add]
  rw [ensemble.operatorAverage_const]
  rw [ensemble.operatorAverage_clean_mul_impurity_mul_clean_eq_zero
    hcentered energy broadening]
  simp

/-- The exact terminal second-order contribution is the Born correction plus the explicit
higher-order remainder. -/
theorem exactSecondOrderRetardedContribution_eq_born_add_remainder
    (energy broadening : ℝ) :
    ensemble.exactSecondOrderRetardedContribution energy broadening =
      ensemble.bornRetardedCorrection energy broadening +
        ensemble.bornRetardedRemainder energy broadening := by
  unfold exactSecondOrderRetardedContribution bornRetardedCorrection
    bornRetardedRemainder
  have hfunctions :
      (fun ω =>
        ensemble.configurationRetardedResolvent energy broadening ω *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening *
          (ensemble.impurityPotential ω).1 *
          ensemble.cleanRetardedResolvent energy broadening) =
        (fun ω =>
          ensemble.cleanRetardedResolvent energy broadening *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening +
            (ensemble.configurationRetardedResolvent energy broadening ω -
                ensemble.cleanRetardedResolvent energy broadening) *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening *
              (ensemble.impurityPotential ω).1 *
              ensemble.cleanRetardedResolvent energy broadening) := by
    funext ω
    noncomm_ring
  rw [hfunctions]
  exact ensemble.operatorAverage_add _ _

/-- Exact finite-dimensional relation between the averaged resolvent, the named Born
approximation, and the retained remainder. Dropping the final term is the approximation step. -/
theorem averagedRetardedResolvent_eq_bornApproximation_add_remainder
    (hcentered : ensemble.IsCentered)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    ensemble.averagedRetardedResolvent energy broadening =
      ensemble.bornAveragedRetardedResolventApproximation energy broadening +
        ensemble.bornRetardedRemainder energy broadening := by
  rw [ensemble.averagedRetardedResolvent_eq_clean_add_exactSecondOrder
    hcentered energy broadening hbroadening]
  rw [ensemble.exactSecondOrderRetardedContribution_eq_born_add_remainder]
  unfold bornAveragedRetardedResolventApproximation
  abel

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
