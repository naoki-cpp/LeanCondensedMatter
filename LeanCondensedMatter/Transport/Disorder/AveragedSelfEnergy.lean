import LeanCondensedMatter.Transport.Disorder.Resolvent
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact averaged Green / self-energy bridge

This module connects the exact finite-disorder averaged Green operator to the abstract two-sided
Dyson self-energy relation. At nonzero broadening, positivity of the ensemble weights and the common
half-plane sign of the configuration resolvents imply that the exact averaged Green operator is
injective on an arbitrary Hilbert space. In finite Hilbert-space dimension, injectivity upgrades to
invertibility and therefore defines the canonical exact self-energy

```text
Σ_exact = G₀⁻¹ - Ḡ⁻¹.
```

The dimension-independent conditional bridge remains available when a two-sided inverse of the
averaged Green operator is supplied explicitly. No exact object in this module is identified with
Born or SCBA approximation data.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- The imaginary part of the configuration-resolvent quadratic form has the spectral-side sign.
This is the pointwise Herglotz identity used below to rule out a kernel of the positive-weight
finite disorder average. -/
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

/-- If the exact averaged Green operator annihilates a vector at nonzero broadening, that vector is
zero. -/
private theorem eq_zero_of_averagedGreen_apply_eq_zero
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    {v : H} (hv : ensemble.averagedGreen side energy broadening v = 0) :
    v = 0 := by
  classical
  have himZero :
      (inner ℂ (ensemble.averagedGreen side energy broadening v) v).im = 0 := by
    rw [hv]
    simp
  rw [ensemble.im_inner_averagedGreen_apply_self side energy broadening hbroadening v] at himZero
  have hfactor : side.sign * broadening ≠ 0 :=
    mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening
  have hsum :
      ∑ ω, ensemble.probability ω *
          ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 = 0 := by
    exact (mul_eq_zero.mp himZero).resolve_left hfactor
  have hexists : ∃ ω : Ω, 0 < ensemble.probability ω := by
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
  obtain ⟨ω, hprobability⟩ := hexists
  have hterm_nonneg : ∀ ξ : Ω,
      0 ≤ ensemble.probability ξ *
        ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    intro ξ
    exact mul_nonneg (ensemble.probability_nonneg ξ) (sq_nonneg _)
  have hterm_le :
      ensemble.probability ω *
          ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 ≤
        ∑ ξ, ensemble.probability ξ *
          ‖ensemble.configurationGreen side energy broadening ξ v‖ ^ 2 := by
    exact Finset.single_le_sum (fun ξ _ => hterm_nonneg ξ) (by simp)
  rw [hsum] at hterm_le
  have hnormSq : ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 = 0 := by
    have hproduct :
        ensemble.probability ω *
            ‖ensemble.configurationGreen side energy broadening ω v‖ ^ 2 = 0 := by
      exact le_antisymm hterm_le (hterm_nonneg ω)
    exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hprobability)
  have hgreenZero : ensemble.configurationGreen side energy broadening ω v = 0 := by
    rw [← norm_eq_zero]
    nlinarith [sq_nonneg ‖ensemble.configurationGreen side energy broadening ω v‖]
  have hleft :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
          (ensemble.configurationHamiltonian ω).1) *
        ensemble.configurationGreen side energy broadening ω = 1 := by
    simpa [FiniteDisorderEnsemble.configurationGreen] using
      spectralShift_mul_spectralResolvent side
        (ensemble.configurationHamiltonian ω).1
        (ensemble.configurationHamiltonian ω).2
        energy broadening hbroadening
  have happly := congrArg (fun operator : H →L[ℂ] H => operator v) hleft
  have hshiftApply :
      (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
          (ensemble.configurationHamiltonian ω).1)
        (ensemble.configurationGreen side energy broadening ω v) = v := by
    simpa using happly
  rw [hgreenZero] at hshiftApply
  simpa using hshiftApply.symm

/-- At nonzero broadening the exact positive-weight finite disorder average of side-indexed
configuration Green operators has trivial kernel, in any Hilbert-space dimension. -/
theorem averagedGreen_injective
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    Function.Injective (ensemble.averagedGreen side energy broadening) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply ensemble.eq_zero_of_averagedGreen_apply_eq_zero side energy broadening hbroadening
  rw [map_sub, hvw, sub_self]

/-- In finite Hilbert-space dimension, the exact averaged Green operator is a unit at every nonzero
broadening. This upgrades the dimension-independent injectivity theorem using finite-dimensional
injective-surjective equivalence. -/
theorem averagedGreen_isUnit
    [FiniteDimensional ℂ H]
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IsUnit (ensemble.averagedGreen side energy broadening) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hinjective := ensemble.averagedGreen_injective side energy broadening hbroadening
  exact ⟨hinjective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjective⟩

/-- If `averagedInverse` is a two-sided inverse of the exact averaged Green operator, then a
candidate self-energy satisfies the exact two-sided Dyson relation exactly when it is the difference
between the clean spectral shift and `averagedInverse`.

The nonzero-broadening hypothesis supplies the two-sided inverse of the clean Green operator. -/
theorem averagedGreen_isSelfEnergy_iff_eq_inverse_sub_inverse
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (averagedInverse selfEnergy : H →L[ℂ] H)
    (haveragedLeft :
      averagedInverse * ensemble.averagedGreen side energy broadening = 1)
    (haveragedRight :
      ensemble.averagedGreen side energy broadening * averagedInverse = 1) :
    IsSelfEnergy
        (ensemble.freeGreen side energy broadening)
        (ensemble.averagedGreen side energy broadening)
        selfEnergy ↔
      selfEnergy =
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
            ensemble.baseHamiltonian.1) - averagedInverse := by
  let freeInverse : H →L[ℂ] H :=
    algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
      ensemble.baseHamiltonian.1
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
  have hiff := IsSelfEnergy.iff_eq_inverse_sub_inverse
    (freeGreen := ensemble.freeGreen side energy broadening)
    (dressedGreen := ensemble.averagedGreen side energy broadening)
    (selfEnergy := selfEnergy)
    (freeInverse := freeInverse)
    (dressedInverse := averagedInverse)
    hfreeLeft hfreeRight haveragedLeft haveragedRight
  simpa [freeInverse] using hiff

/-- A supplied two-sided inverse of the exact averaged Green operator produces an exact Dyson
self-energy through the inverse-difference formula. -/
theorem averagedGreen_inverseDifference_isSelfEnergy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0)
    (averagedInverse : H →L[ℂ] H)
    (haveragedLeft :
      averagedInverse * ensemble.averagedGreen side energy broadening = 1)
    (haveragedRight :
      ensemble.averagedGreen side energy broadening * averagedInverse = 1) :
    IsSelfEnergy
      (ensemble.freeGreen side energy broadening)
      (ensemble.averagedGreen side energy broadening)
      ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
          ensemble.baseHamiltonian.1) - averagedInverse) := by
  apply (ensemble.averagedGreen_isSelfEnergy_iff_eq_inverse_sub_inverse
    side energy broadening hbroadening averagedInverse
    ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
        ensemble.baseHamiltonian.1) - averagedInverse)
    haveragedLeft haveragedRight).2
  rfl

/-- Canonical exact finite-disorder self-energy in finite Hilbert-space dimension at nonzero
broadening. Its inverse is extracted from the proved unit structure of the exact averaged Green
operator, so the finite-dimensional and nonzero-broadening hypotheses are genuine construction
data rather than unused domain markers. -/
noncomputable def exactSelfEnergy
    [FiniteDimensional ℂ H]
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    H →L[ℂ] H := by
  let hunit : IsUnit (ensemble.averagedGreen side energy broadening) :=
    ensemble.averagedGreen_isUnit side energy broadening hbroadening
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  exact
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
        ensemble.baseHamiltonian.1) - averagedInverse

/-- The canonical exact finite-disorder self-energy satisfies the exact two-sided Dyson relation. -/
theorem exactSelfEnergy_isSelfEnergy
    [FiniteDimensional ℂ H]
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    IsSelfEnergy
      (ensemble.freeGreen side energy broadening)
      (ensemble.averagedGreen side energy broadening)
      (ensemble.exactSelfEnergy side energy broadening hbroadening) := by
  let hunit : IsUnit (ensemble.averagedGreen side energy broadening) :=
    ensemble.averagedGreen_isUnit side energy broadening hbroadening
  let averagedUnit : (H →L[ℂ] H)ˣ := hunit.unit
  let averagedInverse : H →L[ℂ] H := ↑(averagedUnit⁻¹)
  change
    IsSelfEnergy
      (ensemble.freeGreen side energy broadening)
      (ensemble.averagedGreen side energy broadening)
      ((algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
          ensemble.baseHamiltonian.1) - averagedInverse)
  apply ensemble.averagedGreen_inverseDifference_isSelfEnergy
    side energy broadening hbroadening averagedInverse
  · simpa [averagedInverse, averagedUnit] using hunit.val_inv_mul
  · simpa [averagedInverse, averagedUnit] using hunit.mul_val_inv

/-- In finite dimension and at nonzero broadening, the canonical exact self-energy is the unique
self-energy satisfying the exact two-sided Dyson relation for the clean and disorder-averaged Green
operators. -/
theorem isSelfEnergy_iff_eq_exactSelfEnergy
    [FiniteDimensional ℂ H]
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
  change
    IsSelfEnergy
        (ensemble.freeGreen side energy broadening)
        (ensemble.averagedGreen side energy broadening)
        selfEnergy ↔
      selfEnergy =
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
            ensemble.baseHamiltonian.1) - averagedInverse
  have hleft : averagedInverse * ensemble.averagedGreen side energy broadening = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.val_inv_mul
  have hright : ensemble.averagedGreen side energy broadening * averagedInverse = 1 := by
    simpa [averagedInverse, averagedUnit] using hunit.mul_val_inv
  exact ensemble.averagedGreen_isSelfEnergy_iff_eq_inverse_sub_inverse
    side energy broadening hbroadening averagedInverse selfEnergy hleft hright

end FiniteDisorderEnsemble

end

end Transport
end QuantumTheory
