import LeanCondensedMatter.Transport.Disorder.Born
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Uniform fixed-regulator error bound for centered finite-disorder Born transport

At a nonzero signed regulator, both the clean and each configuration-dependent self-adjoint
resolvent have operator norm at most `|γ|⁻¹`. Thus the exact cubic remainder in the
centered Born expansion is bounded by the *third absolute impurity norm moment*:

```text
‖Ḡ(E,γ) - (G₀(E,γ) + G₀(E,γ) Σ_B(E,γ) G₀(E,γ))‖
    ≤ |γ|⁻⁴ E[‖Vω‖³].
```

This bound does not require small impurity potentials or convergence of a diagrammatic series,
but is not uniform as `γ → 0`. In particular, it is not an AHE/DC transport limit.
-/

namespace QuantumTheory.Transport

open scoped BigOperators

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Normalized third absolute operator-norm moment of the finite impurity ensemble. -/
noncomputable def impurityThirdNormMoment : ℝ :=
  ∑ ω, ensemble.probability ω * ‖(ensemble.impurityPotential ω).1‖ ^ 3

private theorem norm_mul_seven_le
    (a b c d e f g : H →L[ℂ] H) :
    ‖a * b * c * d * e * f * g‖ ≤
      ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
  calc
    _ ≤ ‖a * b * c * d * e * f‖ * ‖g‖ := norm_mul_le _ _
    _ ≤ ‖a * b * c * d * e‖ * ‖f‖ * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ‖a * b * c * d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ‖a * b * c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ‖a * b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ * ‖f‖ * ‖g‖ := by
      gcongr
      exact norm_mul_le _ _

/-- Fixed-regulator norm bound on the exact finite-ensemble cubic remainder appearing
in the centered Born expansion, independent of a separate centering hypothesis. -/
theorem norm_exactBornRemainder_le_thirdNormMoment
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    ‖ensemble.average (fun ω =>
      ensemble.freeGreenOfRegulator energy regulator *
        (ensemble.impurityPotential ω).1 *
        ensemble.freeGreenOfRegulator energy regulator *
        (ensemble.impurityPotential ω).1 *
        ensemble.configurationGreenOfRegulator energy regulator ω *
        (ensemble.impurityPotential ω).1 *
        ensemble.freeGreenOfRegulator energy regulator)‖ ≤
      |regulator|⁻¹ ^ 4 * ensemble.impurityThirdNormMoment := by
  let B : ℝ := |regulator|⁻¹
  let G₀ := ensemble.freeGreenOfRegulator energy regulator
  let V : Ω → H →L[ℂ] H := fun ω => (ensemble.impurityPotential ω).1
  let G : Ω → H →L[ℂ] H :=
    fun ω => ensemble.configurationGreenOfRegulator energy regulator ω
  let remainder : Ω → H →L[ℂ] H :=
    fun ω => G₀ * V ω * G₀ * V ω * G ω * V ω * G₀
  have hfree : ‖G₀‖ ≤ B := by
    exact norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy regulator hregulator
  have hconfig (ω : Ω) : ‖G ω‖ ≤ B := by
    exact norm_resolvent_spectralParameterOfRegulator_le
      (ensemble.configurationHamiltonian ω).1
      (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  have hpoint (ω : Ω) : ‖remainder ω‖ ≤ B ^ 4 * ‖V ω‖ ^ 3 := by
    calc
      ‖remainder ω‖ ≤
          ‖G₀‖ * ‖V ω‖ * ‖G₀‖ * ‖V ω‖ * ‖G ω‖ * ‖V ω‖ * ‖G₀‖ := by
            exact norm_mul_seven_le G₀ (V ω) G₀ (V ω) (G ω) (V ω) G₀
      _ ≤ B * ‖V ω‖ * B * ‖V ω‖ * B * ‖V ω‖ * B := by
        gcongr
        · exact hfree
        · exact hfree
        · exact hconfig ω
        · exact hfree
      _ = B ^ 4 * ‖V ω‖ ^ 3 := by ring
  change ‖ensemble.average remainder‖ ≤ B ^ 4 *
    (∑ ω, ensemble.probability ω * ‖V ω‖ ^ 3)
  calc
    ‖ensemble.average remainder‖ =
        ‖∑ ω, (ensemble.probability ω : ℂ) • remainder ω‖ := rfl
    _ ≤ ∑ ω, ‖(ensemble.probability ω : ℂ) • remainder ω‖ := norm_sum_le _ _
    _ = ∑ ω, ensemble.probability ω * ‖remainder ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ensemble.probability_nonneg ω)]
    _ ≤ ∑ ω, ensemble.probability ω * (B ^ 4 * ‖V ω‖ ^ 3) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (ensemble.probability_nonneg ω)
    _ = B ^ 4 * (∑ ω, ensemble.probability ω * ‖V ω‖ ^ 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

/-- The exact quenched Green operator is within the third norm moment of its centered
second-order Born approximation at every nonzero signed regulator. -/
theorem norm_averagedGreen_sub_bornSecondOrder_le
    (energy regulator : ℝ) (hregulator : regulator ≠ 0)
    (hcentered : ensemble.IsCentered) :
    ‖ensemble.averagedGreenOfRegulator energy regulator -
      (ensemble.freeGreenOfRegulator energy regulator +
        ensemble.freeGreenOfRegulator energy regulator *
          ensemble.bornSelfEnergyOfRegulator energy regulator *
            ensemble.freeGreenOfRegulator energy regulator)‖ ≤
      |regulator|⁻¹ ^ 4 * ensemble.impurityThirdNormMoment := by
  have hdecomp := ensemble.averagedGreenOfRegulator_eq_born_add_exactRemainder_of_centered
    energy regulator hregulator hcentered
  have herr :
      ensemble.averagedGreenOfRegulator energy regulator -
        (ensemble.freeGreenOfRegulator energy regulator +
          ensemble.freeGreenOfRegulator energy regulator *
            ensemble.bornSelfEnergyOfRegulator energy regulator *
              ensemble.freeGreenOfRegulator energy regulator) =
      ensemble.average (fun ω =>
        ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
          ensemble.freeGreenOfRegulator energy regulator *
          (ensemble.impurityPotential ω).1 *
          ensemble.configurationGreenOfRegulator energy regulator ω *
          (ensemble.impurityPotential ω).1 *
          ensemble.freeGreenOfRegulator energy regulator) := by
    rw [hdecomp]
    abel
  rw [herr]
  exact ensemble.norm_exactBornRemainder_le_thirdNormMoment energy regulator hregulator

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
