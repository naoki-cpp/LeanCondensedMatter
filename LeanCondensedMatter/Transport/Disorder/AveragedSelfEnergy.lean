import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact averaged Green / self-energy bridge

This module connects the exact finite-disorder averaged Green operator to the abstract two-sided
Dyson self-energy relation. At nonzero broadening, positivity of the ensemble weights and the common
half-plane sign of the configuration resolvents imply a uniform lower bound for the exact averaged
Green operator. Its adjoint is the opposite-side averaged Green operator and therefore has trivial
kernel, so the averaged Green range is dense. The lower bound makes this enough for invertibility in
an arbitrary Hilbert space and hence defines the canonical exact self-energy

```text
Σ_exact = G₀⁻¹ - Ḡ⁻¹.
```

No exact object in this module is identified with Born or SCBA approximation data.
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

/-- The imaginary part of the configuration-resolvent quadratic form has the spectral-side sign.
This is the pointwise Herglotz identity used below to derive the averaged resolvent lower bound. -/
private theorem im_inner_configurationGreen_apply_self
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (ω : Ω) (v : H) :
    (inner ℂ (ensemble.configurationGreen side energy broadening ω v) v).im =
      side.sign * broadening *
        ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 := by
  let hamiltonian := (ensemble.configurationHamiltonian ω).1
  let green := ensemble.configurationGreen side energy broadening ω
  let w := green v
  have hshift :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
          green = 1 := by
    simpa [hamiltonian, green, FiniteDisorderEnsemble.configurationGreen] using
      spectralShift_mul_spectralResolvent side
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2
        energy broadening hbroadening
  have hshiftApply :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian)
          w = v := by
    have h := congrArg (fun operator : H →L[ℂ] H => operator v) hshift
    simpa [w] using h
  have hshiftApply' :
      spectralParameter side energy broadening • w - hamiltonian w = v := by
    simpa [Algebra.algebraMap_eq_smul_one] using hshiftApply
  have hsymm : (hamiltonian : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (ensemble.configurationHamiltonian ω).2
  have hinner :
      inner ℂ w v =
        inner ℂ w (spectralParameter side energy broadening • w - hamiltonian w) :=
    congrArg (fun x : H => inner ℂ w x) hshiftApply'.symm
  have himHamiltonian : (inner ℂ w (hamiltonian w)).im = 0 :=
    hsymm.im_inner_self_apply w
  have himSelf : (inner ℂ w w).im = 0 := by
    exact inner_self_im (𝕜 := ℂ) w
  have hreSelf : (inner ℂ w w).re = ‖w‖ ^ 2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  change (inner ℂ w v).im = side.sign * broadening * ‖w‖ ^ 2
  rw [hinner, inner_sub_right, inner_smul_right]
  simp only [Complex.sub_im, Complex.mul_im, himHamiltonian, himSelf, hreSelf,
    spectralParameter_im, sub_zero, mul_zero, zero_add]

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

/-- The exact finite disorder average inherits the common Herglotz sign of the configuration
resolvents. -/
private theorem im_inner_averagedGreen_apply_self
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (v : H) :
    (inner ℂ (ensemble.averagedGreen side energy broadening v) v).im =
      side.sign * broadening *
        ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 := by
  change
    (inner ℂ
      (ensemble.operatorAverage
        (fun ω => ensemble.configurationGreen side energy broadening ω) v) v).im = _
  rw [ensemble.inner_operatorAverage_apply
    (fun ω => ensemble.configurationGreen side energy broadening ω) v v]
  change Complex.imCLM
      (∑ ω, (ensemble.probability ω : ℂ) *
        inner ℂ (ensemble.configurationGreen side energy broadening ω v) v) = _
  rw [map_sum]
  change
    (∑ ω, ((ensemble.probability ω : ℂ) *
      inner ℂ (ensemble.configurationGreen side energy broadening ω v) v).im) = _
  calc
    ∑ ω, ((ensemble.probability ω : ℂ) *
        inner ℂ (ensemble.configurationGreen side energy broadening ω v) v).im =
        ∑ ω, ensemble.probability ω *
          (inner ℂ (ensemble.configurationGreen side energy broadening ω v) v).im := by
      apply Finset.sum_congr rfl
      intro ω _
      simp [Complex.mul_im]
    _ = ∑ ω, ensemble.probability ω *
        (side.sign * broadening *
          ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [ensemble.im_inner_configurationGreen_apply_self
        side energy broadening hbroadening ω v]
    _ = side.sign * broadening *
        ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring

/-- The Herglotz sign and one positive-probability resolvent give a uniform inverse-norm bound for
the exact averaged Green operator. -/
private theorem averagedGreen_antilipschitz
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    ∃ c : NNReal, AntilipschitzWith c (ensemble.averagedGreen side energy broadening) := by
  classical
  obtain ⟨ω, hprobability⟩ := ensemble.exists_probability_pos
  let shift : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      (ensemble.configurationHamiltonian ω).1
  let green : H →L[ℂ] H := ensemble.configurationGreen side energy broadening ω
  let averaged : H →L[ℂ] H := ensemble.averagedGreen side energy broadening
  have hdenomPos : 0 < |broadening| * ensemble.probability ω :=
    mul_pos (abs_pos.mpr hbroadening) hprobability
  let Kreal : ℝ := ‖shift‖ ^ 2 / (|broadening| * ensemble.probability ω)
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
    simpa [shift, green, FiniteDisorderEnsemble.configurationGreen] using
      spectralShift_mul_spectralResolvent side
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2
        energy broadening hbroadening
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
        ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    intro ξ
    exact mul_nonneg (ensemble.probability_nonneg ξ) (sq_nonneg _)
  have hsumNonneg :
      0 ≤ ∑ ξ, ensemble.probability ξ *
        ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    exact Finset.sum_nonneg fun ξ _ => hterm_nonneg ξ
  have htermLe :
      ensemble.probability ω * ‖green v‖ ^ 2 ≤
        ∑ ξ, ensemble.probability ξ *
          ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    simpa [green] using
      (Finset.single_le_sum (fun ξ _ => hterm_nonneg ξ) (by simp) :
        ensemble.probability ω *
            ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 ≤ _)
  have himAbs :
      |(inner ℂ (averaged v) v).im| =
        |broadening| *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    rw [show (inner ℂ (averaged v) v).im =
        side.sign * broadening *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 by
      simpa [averaged] using
        ensemble.im_inner_averagedGreen_apply_self side energy broadening hbroadening v]
    rw [abs_mul, abs_mul, abs_of_nonneg hsumNonneg]
    have hsignAbs : |side.sign| = 1 := by
      cases side <;> norm_num [SpectralSide.sign]
    rw [hsignAbs, one_mul]
  have himLe :
      |(inner ℂ (averaged v) v).im| ≤ ‖averaged v‖ * ‖v‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hsumLe :
      |broadening| *
          ∑ ξ, ensemble.probability ξ *
            ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 ≤
        ‖averaged v‖ * ‖v‖ := by
    rw [← himAbs]
    exact himLe
  have hscaledVSq :
      |broadening| * ensemble.probability ω * ‖v‖ ^ 2 ≤
        ‖shift‖ ^ 2 *
          (|broadening| *
            ∑ ξ, ensemble.probability ξ *
              ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2) := by
    calc
      |broadening| * ensemble.probability ω * ‖v‖ ^ 2 ≤
          |broadening| * ensemble.probability ω *
            (‖shift‖ ^ 2 * ‖green v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hvSqLe
          (mul_nonneg (abs_nonneg broadening) hprobability.le)
      _ = ‖shift‖ ^ 2 *
          (|broadening| *
            (ensemble.probability ω * ‖green v‖ ^ 2)) := by ring
      _ ≤ ‖shift‖ ^ 2 *
          (|broadening| *
            ∑ ξ, ensemble.probability ξ *
              ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left htermLe (abs_nonneg broadening)
  have hcore :
      |broadening| * ensemble.probability ω * ‖v‖ ^ 2 ≤
        ‖shift‖ ^ 2 * (‖averaged v‖ * ‖v‖) :=
    hscaledVSq.trans (mul_le_mul_of_nonneg_left hsumLe (sq_nonneg _))
  have hcancel :
      (|broadening| * ensemble.probability ω) * ‖v‖ ≤
        ‖shift‖ ^ 2 * ‖averaged v‖ := by
    apply (mul_le_mul_iff_right₀ hvnormPos).mp
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hbound : ‖v‖ ≤ Kreal * ‖averaged v‖ := by
    have hdiv :
        ‖v‖ ≤ (‖shift‖ ^ 2 * ‖averaged v‖) /
            (|broadening| * ensemble.probability ω) := by
      apply (le_div_iff₀ hdenomPos).2
      simpa [mul_comm] using hcancel
    calc
      ‖v‖ ≤ (‖shift‖ ^ 2 * ‖averaged v‖) /
          (|broadening| * ensemble.probability ω) := hdiv
      _ = Kreal * ‖averaged v‖ := by
        dsimp [Kreal]
        ring
  exact hbound

/-- At nonzero broadening the exact positive-weight finite disorder average of side-indexed
configuration Green operators has trivial kernel, in any Hilbert-space dimension. -/
private theorem averagedGreen_injective
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Function.Injective (ensemble.averagedGreen side energy broadening) := by
  obtain ⟨_, hantilipschitz⟩ :=
    ensemble.averagedGreen_antilipschitz side energy broadening hbroadening
  exact hantilipschitz.injective

/-- The adjoint averaged Green operator is injective because adjunction exchanges the two spectral
sides and the opposite-side exact average is injective. -/
private theorem star_averagedGreen_injective
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Function.Injective
      ((star (ensemble.averagedGreen side energy broadening) : H →L[ℂ] H)) := by
  rw [ensemble.star_averagedGreen]
  exact ensemble.averagedGreen_injective side.opposite energy broadening hbroadening

/-- At nonzero broadening the exact averaged Green operator has dense range in any Hilbert-space
dimension. -/
private theorem averagedGreen_denseRange
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (ensemble.averagedGreen side energy broadening).range.topologicalClosure = ⊤ := by
  let averaged : H →L[ℂ] H := ensemble.averagedGreen side energy broadening
  let averagedStar : H →L[ℂ] H := star averaged
  have hstarInjective : Function.Injective averagedStar := by
    simpa [averagedStar, averaged] using
      ensemble.star_averagedGreen_injective side energy broadening hbroadening
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

/-- At nonzero broadening, the exact averaged Green operator is a unit in arbitrary Hilbert-space
dimension. The Herglotz identity gives an antilipschitz lower bound, while opposite-side adjunction
gives dense range. -/
theorem averagedGreen_isUnit
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IsUnit (ensemble.averagedGreen side energy broadening) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  apply (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz
    (ensemble.averagedGreen side energy broadening)).2
  exact ⟨ensemble.averagedGreen_denseRange side energy broadening hbroadening,
    ensemble.averagedGreen_antilipschitz side energy broadening hbroadening⟩

/-- Canonical exact finite-disorder self-energy at nonzero broadening in an arbitrary Hilbert space.
Its inverse is extracted from the proved unit structure of the exact averaged Green operator. -/
noncomputable def exactSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    H →L[ℂ] H := by
  let hunit : IsUnit (ensemble.averagedGreen side energy broadening) :=
    ensemble.averagedGreen_isUnit side energy broadening hbroadening
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  exact
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
        ensemble.baseHamiltonian.1) - averagedInverse

/-- At nonzero broadening, the canonical exact self-energy is the unique self-energy satisfying the
exact two-sided Dyson relation for the clean and disorder-averaged Green operators. -/
theorem isSelfEnergy_iff_eq_exactSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (selfEnergy : H →L[ℂ] H) :
    IsSelfEnergy
        (ensemble.freeGreen side energy broadening)
        (ensemble.averagedGreen side energy broadening)
        selfEnergy ↔
      selfEnergy = ensemble.exactSelfEnergy side energy broadening hbroadening := by
  let hunit : IsUnit (ensemble.averagedGreen side energy broadening) :=
    ensemble.averagedGreen_isUnit side energy broadening hbroadening
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  let freeInverse : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      ensemble.baseHamiltonian.1
  change
    IsSelfEnergy
        (ensemble.freeGreen side energy broadening)
        (ensemble.averagedGreen side energy broadening)
        selfEnergy ↔
      selfEnergy = freeInverse - averagedInverse
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
  have haveragedLeft :
      averagedInverse * ensemble.averagedGreen side energy broadening = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.val_inv_mul
  have haveragedRight :
      ensemble.averagedGreen side energy broadening * averagedInverse = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.mul_val_inv
  exact IsSelfEnergy.iff_eq_inverse_sub_inverse
    (freeGreen := ensemble.freeGreen side energy broadening)
    (dressedGreen := ensemble.averagedGreen side energy broadening)
    (selfEnergy := selfEnergy)
    (freeInverse := freeInverse)
    (dressedInverse := averagedInverse)
    hfreeLeft hfreeRight haveragedLeft haveragedRight

/-- The canonical exact finite-disorder self-energy satisfies the exact two-sided Dyson relation. -/
theorem exactSelfEnergy_isSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IsSelfEnergy
      (ensemble.freeGreen side energy broadening)
      (ensemble.averagedGreen side energy broadening)
      (ensemble.exactSelfEnergy side energy broadening hbroadening) := by
  apply (ensemble.isSelfEnergy_iff_eq_exactSelfEnergy
    side energy broadening hbroadening
    (ensemble.exactSelfEnergy side energy broadening hbroadening)).2
  rfl

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
