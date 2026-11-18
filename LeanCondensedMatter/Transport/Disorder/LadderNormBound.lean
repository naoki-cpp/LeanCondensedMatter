import LeanCondensedMatter.Transport.Disorder.FirstRungNormBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Microscopic operator norm and geometric tail of a finite-disorder ladder

The exact finite second moment `C₂(X)=E[Vω X Vω]` and the associated linear
ladder `L(X)=C₂(Gᴸ X Gᴿ)` are bounded in terms of the uniform microscopic
potential norm `M`. In particular, for clean signed-regulator propagators,

```text
‖L‖ ≤ M² / (|γL| |γR|).
```

When the right-hand side is strictly below one, the bounded ladder has a
Neumann-invertible shift `I-L`. The resummed vertex is a fixed point, and
the contribution *after the first rung* has a geometric bound in the norm
of the operator space. No diagrammatic identification with exact disorder
averaging or vanishing-regulator limit is implied.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- For a fixed-point resummed vertex, the part beyond the first ladder rung
is another ladder applied to the dressed-minus-bare difference. -/
theorem resummedLadderVertex_sub_eq_firstRung_add_tail
    (ladder : V →L[ℂ] V) (hinvertible : IsUnit (1 - ladder))
    (bareVertex : V) :
    resummedLadderVertex ladder hinvertible bareVertex - bareVertex =
      ladder bareVertex +
        ladder (resummedLadderVertex ladder hinvertible bareVertex - bareVertex) := by
  let dressed := resummedLadderVertex ladder hinvertible bareVertex
  have hfixed : dressed = bareVertex + ladder dressed :=
    resummedLadderVertex_fixedPoint ladder hinvertible bareVertex
  have hsum : bareVertex + (dressed - bareVertex) = dressed := by abel
  change dressed - bareVertex = ladder bareVertex + ladder (dressed - bareVertex)
  calc
    dressed - bareVertex = ladder dressed := by
      nth_rw 1 [hfixed]
      abel
    _ = ladder (bareVertex + (dressed - bareVertex)) := by rw [hsum]
    _ = ladder bareVertex + ladder (dressed - bareVertex) :=
      map_add ladder _ _

/-- Geometric norm bound on the sum of second and higher ladder rungs, for any
bounded complex-linear ladder fixed point. The upper bound `q < 1`
is explicit and need not equal the exact operator norm. -/
theorem norm_resummedLadderVertex_tail_le
    (ladder : V →L[ℂ] V) (hinvertible : IsUnit (1 - ladder))
    (bareVertex : V) (q : ℝ)
    (hq : ‖ladder‖ ≤ q) (hsmall : q < 1) :
    ‖ladder (resummedLadderVertex ladder hinvertible bareVertex - bareVertex)‖ ≤
      q ^ 2 / (1 - q) * ‖bareVertex‖ := by
  let dressed := resummedLadderVertex ladder hinvertible bareVertex
  have hqnonneg : 0 ≤ q := (norm_nonneg ladder).trans hq
  have hpositive : 0 < 1 - q := sub_pos.mpr hsmall
  have hdecomp : dressed - bareVertex =
      ladder bareVertex + ladder (dressed - bareVertex) :=
    resummedLadderVertex_sub_eq_firstRung_add_tail ladder hinvertible bareVertex
  have haction (x : V) : ‖ladder x‖ ≤ q * ‖x‖ := by
    exact (ladder.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hq (norm_nonneg x))
  have hdiff :
      ‖dressed - bareVertex‖ ≤
        q * ‖bareVertex‖ + q * ‖dressed - bareVertex‖ := by
    calc
      ‖dressed - bareVertex‖ =
          ‖ladder bareVertex + ladder (dressed - bareVertex)‖ := by nth_rw 1 [hdecomp]
      _ ≤ ‖ladder bareVertex‖ + ‖ladder (dressed - bareVertex)‖ :=
        norm_add_le _ _
      _ ≤ q * ‖bareVertex‖ + q * ‖dressed - bareVertex‖ :=
        add_le_add (haction _) (haction _)
  have hlin :
      ‖dressed - bareVertex‖ * (1 - q) ≤ q * ‖bareVertex‖ := by
    nlinarith [hdiff]
  have hratio :
      ‖dressed - bareVertex‖ ≤ (q * ‖bareVertex‖) / (1 - q) :=
    (le_div_iff₀ hpositive).2 hlin
  calc
    ‖ladder (dressed - bareVertex)‖ ≤ q * ‖dressed - bareVertex‖ :=
      haction _
    _ ≤ q * ((q * ‖bareVertex‖) / (1 - q)) :=
      mul_le_mul_of_nonneg_left hratio hqnonneg
    _ = q ^ 2 / (1 - q) * ‖bareVertex‖ := by ring

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

private theorem norm_mul_three_le
    (a b c : H →L[ℂ] H) :
    ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  calc
    _ ≤ ‖a * b‖ * ‖c‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖b‖) * ‖c‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- Microscopic norm control of the exact finite second-moment action. -/
theorem norm_exactSecondMoment_le_uniformPotential_sq
    (kernel : H →L[ℂ] H) (potentialBound : ℝ)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.exactSecondMoment kernel‖ ≤
      potentialBound ^ 2 * ‖kernel‖ := by
  have hbound : 0 ≤ potentialBound :=
    ensemble.uniformPotentialBound_nonneg potentialBound hpotential
  rw [ensemble.exactSecondMoment_eq_average]
  apply ensemble.norm_average_le_of_forall _ _
  intro ω
  let impurity := (ensemble.impurityPotential ω).1
  have hp : ‖impurity‖ ≤ potentialBound := hpotential ω
  change ‖impurity * kernel * impurity‖ ≤
    potentialBound ^ 2 * ‖kernel‖
  calc
    ‖impurity * kernel * impurity‖ ≤
        ‖impurity‖ * ‖kernel‖ * ‖impurity‖ :=
      norm_mul_three_le _ _ _
    _ ≤ potentialBound * ‖kernel‖ * potentialBound := by
      have hfirst : ‖impurity‖ * ‖kernel‖ ≤
          potentialBound * ‖kernel‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg kernel)
      calc
        ‖impurity‖ * ‖kernel‖ * ‖impurity‖ ≤
            (potentialBound * ‖kernel‖) * ‖impurity‖ :=
          mul_le_mul_of_nonneg_right hfirst (norm_nonneg impurity)
        _ ≤ (potentialBound * ‖kernel‖) * potentialBound :=
          mul_le_mul_of_nonneg_left hp
            (mul_nonneg hbound (norm_nonneg kernel))
    _ = potentialBound ^ 2 * ‖kernel‖ := by ring

/-- The supplied finite covariance ladder has norm at most
`M² ‖Gᴸ‖ ‖Gᴿ‖`, without Gaussian or momentum-space assumptions. -/
theorem norm_retardedAdvancedLadderCLM_le_uniformPotential_sq
    (leftGreen rightGreen : H →L[ℂ] H)
    (potentialBound : ℝ)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.retardedAdvancedLadderCLM leftGreen rightGreen‖ ≤
      potentialBound ^ 2 * ‖leftGreen‖ * ‖rightGreen‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (by positivity)
  intro vertex
  change ‖ensemble.exactSecondMoment (leftGreen * vertex * rightGreen)‖ ≤
    (potentialBound ^ 2 * ‖leftGreen‖ * ‖rightGreen‖) * ‖vertex‖
  calc
    ‖ensemble.exactSecondMoment (leftGreen * vertex * rightGreen)‖ ≤
        potentialBound ^ 2 * ‖leftGreen * vertex * rightGreen‖ :=
      ensemble.norm_exactSecondMoment_le_uniformPotential_sq
        _ potentialBound hpotential
    _ ≤ potentialBound ^ 2 *
        (‖leftGreen‖ * ‖vertex‖ * ‖rightGreen‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_three_le _ _ _) (sq_nonneg _)
    _ = (potentialBound ^ 2 * ‖leftGreen‖ * ‖rightGreen‖) *
        ‖vertex‖ := by ring

/-- Explicit microscopic fixed-regulator sufficient bound for small ladder norm.
The clean resolvents have norms at most the inverse absolute regulators. -/
theorem norm_freeGreenLadder_le_uniformPotential_sq
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (potentialBound : ℝ)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound) :
    ‖ensemble.retardedAdvancedLadderCLM
      (ensemble.freeGreenOfRegulator energyLeft regulatorLeft)
      (ensemble.freeGreenOfRegulator energyRight regulatorRight)‖ ≤
      potentialBound ^ 2 * |regulatorLeft|⁻¹ * |regulatorRight|⁻¹ := by
  let freeLeft := ensemble.freeGreenOfRegulator energyLeft regulatorLeft
  let freeRight := ensemble.freeGreenOfRegulator energyRight regulatorRight
  let leftBound : ℝ := |regulatorLeft|⁻¹
  let rightBound : ℝ := |regulatorRight|⁻¹
  have hleft : ‖freeLeft‖ ≤ leftBound :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energyLeft regulatorLeft hregLeft
  have hright : ‖freeRight‖ ≤ rightBound :=
    norm_resolvent_spectralParameterOfRegulator_le
      ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energyRight regulatorRight hregRight
  have hM : 0 ≤ potentialBound ^ 2 := sq_nonneg _
  have hLM : 0 ≤ potentialBound ^ 2 * leftBound :=
    mul_nonneg hM (inv_nonneg.mpr (abs_nonneg regulatorLeft))
  change ‖ensemble.retardedAdvancedLadderCLM freeLeft freeRight‖ ≤
    potentialBound ^ 2 * leftBound * rightBound
  calc
    _ ≤ potentialBound ^ 2 * ‖freeLeft‖ * ‖freeRight‖ :=
      ensemble.norm_retardedAdvancedLadderCLM_le_uniformPotential_sq
        freeLeft freeRight potentialBound hpotential
    _ ≤ potentialBound ^ 2 * leftBound * ‖freeRight‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hleft hM) (norm_nonneg freeRight)
    _ ≤ potentialBound ^ 2 * leftBound * rightBound := by
      exact mul_le_mul_of_nonneg_left hright hLM

/-- The microscopic condition `M²/(|γL| |γR|)<1` makes
`I - L` invertible on the bounded-operator space. -/
theorem isUnit_one_sub_freeGreenLadder_of_smallPotential
    (energyLeft regulatorLeft energyRight regulatorRight : ℝ)
    (hregLeft : regulatorLeft ≠ 0) (hregRight : regulatorRight ≠ 0)
    (potentialBound : ℝ)
    (hpotential : ∀ ω, ‖(ensemble.impurityPotential ω).1‖ ≤ potentialBound)
    (hsmall : potentialBound ^ 2 * |regulatorLeft|⁻¹ *
        |regulatorRight|⁻¹ < 1) :
    IsUnit (1 - ensemble.retardedAdvancedLadderCLM
      (ensemble.freeGreenOfRegulator energyLeft regulatorLeft)
      (ensemble.freeGreenOfRegulator energyRight regulatorRight)) := by
  exact isUnit_one_sub_of_norm_lt_one
    (lt_of_le_of_lt
      (ensemble.norm_freeGreenLadder_le_uniformPotential_sq
        energyLeft regulatorLeft energyRight regulatorRight
        hregLeft hregRight potentialBound hpotential) hsmall)

end FiniteDisorderEnsemble

end
end QuantumTheory.Transport
