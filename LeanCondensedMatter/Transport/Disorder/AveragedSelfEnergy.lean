import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

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

/-- A normalized finite nonnegative probability weight has at least one strictly positive entry. -/
private theorem exists_probability_pos : ∃ ω : Ω, 0 < ensemble.probability ω := by
  by_contra h
  have hle : ∀ ω : Ω, ensemble.probability ω ≤ 0 := by
    intro ω
    exact le_of_not_gt (fun hpos => h ⟨ω, hpos⟩)
  have hzero : ∀ ω : Ω, ensemble.probability ω = 0 := by
    intro ω
    exact le_antisymm (hle ω) (ensemble.probability_nonneg ω)
  have hsumProbability : ∑ ω, ensemble.probability ω = 0 := by
    simp [hzero]
  linarith [ensemble.probability_sum]

/-- The imaginary part of a configuration-resolvent quadratic form equals the signed regulator
multiplied by the squared resolvent norm. -/
private theorem im_inner_configurationGreenOfRegulator_apply_self
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (ω : Ω) (v : H) :
    (inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v).im =
      regulator * ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 := by
  let hamiltonian := (ensemble.configurationHamiltonian ω).1
  let green := ensemble.configurationGreenOfRegulator energy regulator ω
  let w := green v
  have hshift :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) *
          green = 1 := by
    simpa [hamiltonian, green, FiniteDisorderEnsemble.configurationGreenOfRegulator] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2 energy regulator hregulator
  have hshiftApply :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian)
          w = v := by
    have h := congrArg (fun operator : H →L[ℂ] H => operator v) hshift
    simpa [w] using h
  have hshiftApply' :
      spectralParameterOfRegulator energy regulator • w - hamiltonian w = v := by
    simpa [Algebra.algebraMap_eq_smul_one] using hshiftApply
  have hsymm : (hamiltonian : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ensemble.configurationHamiltonian ω).2
  have hinner :
      inner ℂ w v =
        inner ℂ w (spectralParameterOfRegulator energy regulator • w - hamiltonian w) :=
    congrArg (fun x : H => inner ℂ w x) hshiftApply'.symm
  have himHamiltonian : (inner ℂ w (hamiltonian w)).im = 0 :=
    hsymm.im_inner_self_apply w
  have himSelf : (inner ℂ w w).im = 0 := by
    exact inner_self_im (𝕜 := ℂ) w
  have hreSelf : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  change (inner ℂ w v).im = regulator * ‖w‖ ^ 2
  rw [hinner, inner_sub_right, inner_smul_right]
  simp only [Complex.sub_im, Complex.mul_im, himHamiltonian, himSelf, hreSelf,
    spectralParameterOfRegulator_im, sub_zero, mul_zero, zero_add]

/-- Taking an inner product after an exact finite operator average is the corresponding weighted
finite average of inner products. -/
private theorem inner_operatorAverage_apply
    (operator : Ω → H →L[ℂ] H) (v w : H) :
    inner ℂ (ensemble.operatorAverage operator v) w =
      ∑ ω, (ensemble.probability ω : ℂ) * inner ℂ (operator ω v) w := by
  unfold operatorAverage
  rw [sum_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro ω _
  simpa [Algebra.smul_def] using
    (inner_smul_real_left (𝕜 := ℂ) (operator ω v) w (ensemble.probability ω))

/-- The exact finite disorder average inherits the signed-regulator Herglotz identity. -/
private theorem im_inner_averagedGreenOfRegulator_apply_self
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (v : H) :
    (inner ℂ (ensemble.averagedGreenOfRegulator energy regulator v) v).im =
      regulator *
        ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 := by
  change
    (inner ℂ
      (ensemble.operatorAverage
        (fun ω => ensemble.configurationGreenOfRegulator energy regulator ω) v) v).im = _
  rw [ensemble.inner_operatorAverage_apply
    (fun ω => ensemble.configurationGreenOfRegulator energy regulator ω) v v]
  change Complex.imCLM
      (∑ ω, (ensemble.probability ω : ℂ) *
        inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v) = _
  rw [map_sum]
  change
    (∑ ω, ((ensemble.probability ω : ℂ) *
      inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v).im) = _
  calc
    ∑ ω, ((ensemble.probability ω : ℂ) *
        inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v).im =
        ∑ ω, ensemble.probability ω *
          (inner ℂ (ensemble.configurationGreenOfRegulator energy regulator ω v) v).im := by
      apply Finset.sum_congr rfl
      intro ω _
      simp [Complex.mul_im]
    _ = ∑ ω, ensemble.probability ω *
        (regulator * ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [ensemble.im_inner_configurationGreenOfRegulator_apply_self
        energy regulator hregulator ω v]
    _ = regulator *
        ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreenOfRegulator energy regulator ω v‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

/-- The Herglotz identity and one positive-probability resolvent give a uniform inverse-norm bound
for the exact averaged Green operator at any nonzero signed regulator. -/
private theorem averagedGreenOfRegulator_antilipschitz
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    ∃ c : NNReal, AntilipschitzWith c (ensemble.averagedGreenOfRegulator energy regulator) := by
  classical
  obtain ⟨ω, hprobability⟩ := ensemble.exists_probability_pos
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
    have hsq : ‖v‖ ^ 2 ≤ (‖shift‖ * ‖green v‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg v)
        (mul_nonneg (norm_nonneg shift) (norm_nonneg (green v)))).2 hvLe
    calc
      ‖v‖ ^ 2 ≤ (‖shift‖ * ‖green v‖) ^ 2 := hsq
      _ = ‖shift‖ ^ 2 * ‖green v‖ ^ 2 := by ring
  have hterm_nonneg : ∀ ξ : Ω,
      0 ≤ ensemble.probability ξ *
        ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 := by
    intro ξ
    exact mul_nonneg (ensemble.probability_nonneg ξ) (sq_nonneg _)
  have hsumNonneg :
      0 ≤ ∑ ξ, ensemble.probability ξ *
        ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2 := by
    exact Finset.sum_nonneg fun ξ _ => hterm_nonneg ξ
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
  have hscaledVSq :
      |regulator| * ensemble.probability ω * ‖v‖ ^ 2 ≤
        ‖shift‖ ^ 2 *
          (|regulator| *
            ∑ ξ, ensemble.probability ξ *
              ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2) := by
    calc
      |regulator| * ensemble.probability ω * ‖v‖ ^ 2 ≤
          |regulator| * ensemble.probability ω *
            (‖shift‖ ^ 2 * ‖green v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hvSqLe
          (mul_nonneg (abs_nonneg regulator) hprobability.le)
      _ = ‖shift‖ ^ 2 *
          (|regulator| *
            (ensemble.probability ω * ‖green v‖ ^ 2)) := by ring
      _ ≤ ‖shift‖ ^ 2 *
          (|regulator| *
            ∑ ξ, ensemble.probability ξ *
              ‖ensemble.configurationGreenOfRegulator energy regulator ξ v‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left htermLe (abs_nonneg regulator)
  have hcore :
      |regulator| * ensemble.probability ω * ‖v‖ ^ 2 ≤
        ‖shift‖ ^ 2 * (‖averaged v‖ * ‖v‖) :=
    hscaledVSq.trans (mul_le_mul_of_nonneg_left hsumLe (sq_nonneg _))
  have hcancel :
      (|regulator| * ensemble.probability ω) * ‖v‖ ≤
        ‖shift‖ ^ 2 * ‖averaged v‖ := by
    apply (mul_le_mul_iff_right₀ hvnormPos).mp
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hbound : ‖v‖ ≤ Kreal * ‖averaged v‖ := by
    have hdiv :
        ‖v‖ ≤ (‖shift‖ ^ 2 * ‖averaged v‖) /
            (|regulator| * ensemble.probability ω) := by
      apply (le_div_iff₀ hdenomPos).2
      simpa [mul_comm] using hcancel
    calc
      ‖v‖ ≤ (‖shift‖ ^ 2 * ‖averaged v‖) /
          (|regulator| * ensemble.probability ω) := hdiv
      _ = Kreal * ‖averaged v‖ := by
        dsimp [Kreal]
        ring
  exact hbound

private theorem averagedGreenOfRegulator_injective
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Function.Injective (ensemble.averagedGreenOfRegulator energy regulator) := by
  obtain ⟨_, hantilipschitz⟩ :=
    ensemble.averagedGreenOfRegulator_antilipschitz energy regulator hregulator
  exact hantilipschitz.injective

private theorem star_averagedGreenOfRegulator_injective
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    Function.Injective
      ((star (ensemble.averagedGreenOfRegulator energy regulator) : H →L[ℂ] H)) := by
  rw [ensemble.star_averagedGreenOfRegulator]
  exact ensemble.averagedGreenOfRegulator_injective
    energy (-regulator) (neg_ne_zero.mpr hregulator)

private theorem averagedGreenOfRegulator_denseRange
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    (ensemble.averagedGreenOfRegulator energy regulator).range.topologicalClosure = ⊤ := by
  let averaged : H →L[ℂ] H := ensemble.averagedGreenOfRegulator energy regulator
  let averagedStar : H →L[ℂ] H := star averaged
  have hstarInjective : Function.Injective averagedStar := by
    simpa [averagedStar, averaged] using
      ensemble.star_averagedGreenOfRegulator_injective energy regulator hregulator
  have hker : averagedStar.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hstarInjective
  have hadjoint : ContinuousLinearMap.adjoint averagedStar = averaged := by
    change star (star averaged) = averaged
    exact star_star averaged
  change averaged.range.topologicalClosure = ⊤
  calc
    averaged.range.topologicalClosure = averagedStar.kerᗮ := by
      rw [← hadjoint]
      exact (ContinuousLinearMap.orthogonal_ker averagedStar).symm
    _ = ⊤ := by rw [hker]; simp

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
  have hfreeLeft :
      freeInverse * ensemble.freeGreenOfRegulator energy regulator = 1 := by
    simpa [freeInverse, FiniteDisorderEnsemble.freeGreenOfRegulator] using
      spectralShift_mul_resolvent_spectralParameterOfRegulator
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  have hfreeRight :
      ensemble.freeGreenOfRegulator energy regulator * freeInverse = 1 := by
    simpa [freeInverse, FiniteDisorderEnsemble.freeGreenOfRegulator] using
      resolvent_spectralParameterOfRegulator_mul_spectralShift
        ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2 energy regulator hregulator
  have haveragedLeft :
      averagedInverse * ensemble.averagedGreenOfRegulator energy regulator = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.val_inv_mul
  have haveragedRight :
      ensemble.averagedGreenOfRegulator energy regulator * averagedInverse = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.mul_val_inv
  exact IsSelfEnergy.iff_eq_inverse_sub_inverse
    (freeGreen := ensemble.freeGreenOfRegulator energy regulator)
    (dressedGreen := ensemble.averagedGreenOfRegulator energy regulator)
    (selfEnergy := selfEnergy)
    (freeInverse := freeInverse)
    (dressedInverse := averagedInverse)
    hfreeLeft hfreeRight haveragedLeft haveragedRight

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
