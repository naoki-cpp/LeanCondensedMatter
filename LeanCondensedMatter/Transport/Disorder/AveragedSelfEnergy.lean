import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Exact averaged Green / self-energy bridge

This module connects the exact finite-disorder averaged Green operator to the abstract two-sided
Dyson self-energy relation. At any nonzero signed regulator `γ`, positivity of the ensemble weights
and the common half-plane sign of the configuration resolvents imply a uniform lower bound for the
exact averaged Green operator. Its adjoint is the averaged Green operator at `-γ` and therefore has
trivial kernel, so the averaged Green range is dense. The lower bound makes this enough for
invertibility in an arbitrary Hilbert space and hence defines the canonical exact self-energy

```text
Σ_exact(E, γ) = G₀(E, γ)⁻¹ - Ḡ(E, γ)⁻¹.
```

Physical consumers specialize the signed regulator locally when retarded/advanced branch semantics
are needed. No exact object in this module is identified with Born or SCBA approximation data.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The exact finite disorder average inherits the signed-regulator Herglotz identity. -/
private theorem im_inner_averagedGreenOfRegulator_apply_self
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (v : H) :
    (inner ℂ (ensemble.averagedGreenOfRegulator energy regulator v) v).im =
      regulator *
        ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 := by
  have hinner :
      inner ℂ (ensemble.averagedGreenOfRegulator energy regulator v) v =
        ∑ ω, (ensemble.probability ω : ℂ) *
          inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v := by
    change inner ℂ ((∑ ω, (ensemble.probability ω : ℂ) •
      ensemble.configurationGreenOfRegulator energy regulator ω) v) v = _
    rw [sum_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro ω _
    simpa [Algebra.smul_def] using
      (inner_smul_real_left (𝕜 := ℂ)
        (ensemble.configurationGreenOfRegulator energy regulator ω v) v
        (ensemble.probability ω))
  rw [hinner, Complex.im_sum]
  have him (ω : Ω) :
      (inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v).im =
        regulator * ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 := by
    simpa only [FiniteDisorderEnsemble.configurationGreenOfRegulator] using
      im_inner_resolvent_spectralParameterOfRegulator_apply_self
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2 energy regulator hregulator v
  simp_rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, him]
  simp_rw [mul_left_comm (ensemble.probability _) regulator]
  rw [← Finset.mul_sum]

/-- The Herglotz identity and one positive-probability resolvent give a uniform inverse-norm bound
for the exact averaged Green operator at any nonzero signed regulator. -/
private theorem averagedGreenOfRegulator_antilipschitz
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    ∃ c : NNReal, AntilipschitzWith c (ensemble.averagedGreenOfRegulator energy regulator) := by
  classical
  obtain ⟨ω, _, hprobability⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun ω _ => ensemble.probability_nonneg ω)).mp
      (by rw [ensemble.probability_sum]; norm_num)
  let shift : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      (ensemble.configurationHamiltonian ω).1
  let green : H →L[ℂ] H := ensemble.configurationGreenOfRegulator energy regulator ω
  let averaged : H →L[ℂ] H := ensemble.averagedGreenOfRegulator energy regulator
  have hdenomPos : 0 < |regulator| * ensemble.probability ω :=
    mul_pos (abs_pos.mpr hregulator) hprobability
  let Kreal : ℝ := ‖shift‖ ^ 2 / (|regulator| * ensemble.probability ω)
  have hKnonneg : 0 ≤ Kreal := by
    dsimp [Kreal]
    exact div_nonneg (sq_nonneg _) hdenomPos.le
  let K : NNReal := ⟨Kreal, hKnonneg⟩
  refine ⟨K, ContinuousLinearMap.antilipschitz_of_bound averaged ?_⟩
  intro v
  change ‖v‖ ≤ (K : ℝ) * ‖averaged v‖
  change ‖v‖ ≤ Kreal * ‖averaged v‖
  by_cases hv : v = 0
  · simp [hv]
  have hvnormPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hleft : shift * green = 1 := by
    simpa [shift, green, FiniteDisorderEnsemble.configurationGreenOfRegulator] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  have hshiftApply : shift (green v) = v := by
    have h := congrArg (fun operator : H →L[ℂ] H => operator v) hleft
    simpa using h
  have hvLe : ‖v‖ ≤ ‖shift‖ * ‖green v‖ := by
    calc
      ‖v‖ = ‖shift (green v)‖ := by rw [hshiftApply]
      _ ≤ ‖shift‖ * ‖green v‖ := ContinuousLinearMap.le_opNorm shift (green v)
  have hvSqLe : ‖v‖ ^ 2 ≤ ‖shift‖ ^ 2 * ‖green v‖ ^ 2 := by
    calc
      _ ≤ (‖shift‖ * ‖green v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg v)
          (mul_nonneg (norm_nonneg shift) (norm_nonneg (green v)))).2 hvLe
      _ = _ := by ring
  have hterm_nonneg (ξ : Ω) :
      0 ≤ ensemble.probability ξ *
        ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 :=
    mul_nonneg (ensemble.probability_nonneg ξ) (sq_nonneg _)
  have hsumNonneg :
      0 ≤ ∑ ξ, ensemble.probability ξ *
        ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 :=
    Finset.sum_nonneg fun ξ _ => hterm_nonneg ξ
  have htermLe :
      ensemble.probability ω * ‖green v‖ ^ 2 ≤
        ∑ ξ, ensemble.probability ξ *
          ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 := by
    simpa [green] using
      (Finset.single_le_sum (fun ξ _ => hterm_nonneg ξ) (by simp) :
        ensemble.probability ω *
            ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 ≤ _)
  have himAbs :
      |(inner ℂ (averaged v) v).im| =
        |regulator| *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 := by
    rw [show (inner ℂ (averaged v) v).im =
        regulator *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 by
      simpa [averaged] using
        ensemble.im_inner_averagedGreenOfRegulator_apply_self
          energy regulator hregulator v]
    rw [abs_mul, abs_of_nonneg hsumNonneg]
  have himLe :
      |(inner ℂ (averaged v) v).im| ≤ ‖averaged v‖ * ‖v‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hsumLe :
      |regulator| *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 ≤
        ‖averaged v‖ * ‖v‖ := by
    rw [← himAbs]
    exact himLe
  have hcore :
      |regulator| * ensemble.probability ω * ‖v‖ ^ 2 ≤
        ‖shift‖ ^ 2 * (‖averaged v‖ * ‖v‖) := by
    calc
      _ ≤ |regulator| * ensemble.probability ω *
            (‖shift‖ ^ 2 * ‖green v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hvSqLe hdenomPos.le
      _ = ‖shift‖ ^ 2 *
            (|regulator| * (ensemble.probability ω * ‖green v‖ ^ 2)) := by ring
      _ ≤ ‖shift‖ ^ 2 *
            (|regulator| *
              ∑ ξ, ensemble.probability ξ *
                ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htermLe (abs_nonneg _)) (sq_nonneg _)
      _ ≤ ‖shift‖ ^ 2 * (‖averaged v‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hsumLe (sq_nonneg _)
  have hcancel :
      (|regulator| * ensemble.probability ω) * ‖v‖ ≤
        ‖shift‖ ^ 2 * ‖averaged v‖ := by
    apply (mul_le_mul_iff_right₀ hvnormPos).mp
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcore
  calc
    ‖v‖ ≤ (‖shift‖ ^ 2 * ‖averaged v‖) /
        (|regulator| * ensemble.probability ω) :=
      (le_div_iff₀ hdenomPos).2 (by simpa [mul_comm] using hcancel)
    _ = Kreal * ‖averaged v‖ := by dsimp [Kreal]; ring

private theorem averagedGreenOfRegulator_denseRange
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    (ensemble.averagedGreenOfRegulator energy regulator).range.topologicalClosure = ⊤ := by
  let averaged : H →L[ℂ] H := ensemble.averagedGreenOfRegulator energy regulator
  have hstarInjective : Function.Injective
      (star averaged : H →L[ℂ] H) := by
    obtain ⟨_, hanti⟩ :=
      ensemble.averagedGreenOfRegulator_antilipschitz
        energy (-regulator) (neg_ne_zero.mpr hregulator)
    simpa only [averaged, ensemble.star_averagedGreenOfRegulator] using
      hanti.injective
  change averaged.range.topologicalClosure = ⊤
  calc
    averaged.range.topologicalClosure = (star averaged).kerᗮ := by
      simpa only [← ContinuousLinearMap.star_eq_adjoint, star_star] using
        (ContinuousLinearMap.orthogonal_ker (star averaged)).symm
    _ = ⊤ := by
      rw [LinearMap.ker_eq_bot.mpr hstarInjective]
      simp

/-- At any nonzero signed regulator the exact averaged Green operator is a unit in arbitrary
Hilbert-space dimension. -/
theorem averagedGreenOfRegulator_isUnit
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    IsUnit (ensemble.averagedGreenOfRegulator energy regulator) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  apply (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz
    (ensemble.averagedGreenOfRegulator energy regulator)).2
  exact ⟨ensemble.averagedGreenOfRegulator_denseRange energy regulator hregulator,
    ensemble.averagedGreenOfRegulator_antilipschitz energy regulator hregulator⟩

/-- Canonical exact finite-disorder self-energy at an arbitrary nonzero signed regulator. -/
noncomputable def exactSelfEnergyOfRegulator
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) : H →L[ℂ] H := by
  let hunit : IsUnit (ensemble.averagedGreenOfRegulator energy regulator) :=
    ensemble.averagedGreenOfRegulator_isUnit energy regulator hregulator
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  exact
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
        ensemble.baseHamiltonian.1) - averagedInverse

/-- At a nonzero signed regulator, the canonical exact self-energy is the unique self-energy
satisfying the exact two-sided Dyson relation for the clean and disorder-averaged Green operators. -/
theorem isSelfEnergy_iff_eq_exactSelfEnergyOfRegulator
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (selfEnergy : H →L[ℂ] H) :
    IsSelfEnergy
        (ensemble.freeGreenOfRegulator energy regulator)
        (ensemble.averagedGreenOfRegulator energy regulator)
        selfEnergy ↔
      selfEnergy = ensemble.exactSelfEnergyOfRegulator energy regulator hregulator := by
  let hunit : IsUnit (ensemble.averagedGreenOfRegulator energy regulator) :=
    ensemble.averagedGreenOfRegulator_isUnit energy regulator hregulator
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  let freeInverse : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) -
      ensemble.baseHamiltonian.1
  change
    IsSelfEnergy
        (ensemble.freeGreenOfRegulator energy regulator)
        (ensemble.averagedGreenOfRegulator energy regulator)
        selfEnergy ↔
      selfEnergy = freeInverse - averagedInverse
  refine IsSelfEnergy.iff_eq_inverse_sub_inverse
    (freeGreen := ensemble.freeGreenOfRegulator energy regulator)
    (dressedGreen := ensemble.averagedGreenOfRegulator energy regulator)
    (selfEnergy := selfEnergy)
    (freeInverse := freeInverse)
    (dressedInverse := averagedInverse) ?_ ?_ ?_ ?_
  · simpa [freeInverse, FiniteDisorderEnsemble.freeGreenOfRegulator] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  · simpa [freeInverse, FiniteDisorderEnsemble.freeGreenOfRegulator] using
      resolvent_spectralParameterOfRegulator_mul_spectralShift
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  · simpa [averagedInverse, averagedUnit] using hunit.val_inv_mul
  · simpa [averagedInverse, averagedUnit] using hunit.mul_val_inv

/-- The canonical exact finite-disorder self-energy satisfies the exact two-sided Dyson relation at
any nonzero signed regulator. -/
theorem exactSelfEnergyOfRegulator_isSelfEnergy
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    IsSelfEnergy
      (ensemble.freeGreenOfRegulator energy regulator)
      (ensemble.averagedGreenOfRegulator energy regulator)
      (ensemble.exactSelfEnergyOfRegulator energy regulator hregulator) := by
  apply (ensemble.isSelfEnergy_iff_eq_exactSelfEnergyOfRegulator
    energy regulator hregulator
    (ensemble.exactSelfEnergyOfRegulator energy regulator hregulator)).2
  rfl

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
